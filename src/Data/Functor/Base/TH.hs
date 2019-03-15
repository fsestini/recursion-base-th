{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module Data.Functor.Base.TH (mkBaseFunctor) where

import Control.Monad
import Language.Haskell.TH
import Control.Monad.Reader
import Data.Functor.Identity
import Data.Functor.Foldable

varName :: TyVarBndr -> Name
varName (PlainTV nm) = nm
varName (KindedTV nm _) = nm

mkBaseFunctor :: Name -> Q [Dec]
mkBaseFunctor name = do
  TyConI (DataD _ _ vars _ cs _) <- reify name
  x <- newName "x"
  cs' <- runReaderT (mapM aux cs) (Things name (fmap varName vars) x)
  clauses <- mapM genClause cs
  clauses' <- mapM genClause' cs
  let fullyApplied = appsT name vars
  pure $
    [ DataD [] (appendF name) (vars ++ [PlainTV x])
        Nothing cs' [DerivClause Nothing [ConT ''Functor, ConT ''Foldable, ConT ''Traversable]]
    , TySynInstD ''Base (TySynEqn [fullyApplied] (appsT (appendF name) vars))
    , InstanceD Nothing [] (ConT ''Recursive `AppT` fullyApplied)
        [FunD (mkName "project") clauses]
    , InstanceD Nothing [] (ConT ''Corecursive `AppT` fullyApplied)
        [FunD (mkName "embed") clauses']
    ]
  where
    appsT nm vs = foldl AppT (ConT nm) (fmap (VarT . varName) vs)

    fromNormalCtor name fieldTypes = do
      fieldNames <- replicateM (length fieldTypes) (newName "x")
      let pat = conP name (fmap varP fieldNames)
          body = normalB . appsE $ conE (appendF name) : fmap varE fieldNames
      clause [pat] body []

    fromNormalCtor' name fieldTypes = do
      fieldNames <- replicateM (length fieldTypes) (newName "x")
      let pat = conP (appendF name) (fmap varP fieldNames)
          body = normalB . appsE $ conE name : fmap varE fieldNames
      clause [pat] body []

    genClause :: Con -> Q Clause
    genClause (NormalC name fieldTypes) = fromNormalCtor name fieldTypes
    genClause (RecC name fieldTypes) = fromNormalCtor name fieldTypes
    genClause (InfixC ty1 name ty2) = do
      x1 <- newName "x"
      x2 <- newName "x"
      let pat = infixP (varP x1) name (varP x2)
          body = normalB $
            infixE (Just (varE x1)) (varE (appendColon name)) (Just (varE x2))
      clause [pat] body []

    genClause' :: Con -> Q Clause
    genClause' (NormalC name fieldTypes) = fromNormalCtor' name fieldTypes
    genClause' (RecC name fieldTypes) = fromNormalCtor' name fieldTypes
    genClause' (InfixC ty1 name ty2) = do
      x1 <- newName "x"
      x2 <- newName "x"
      let pat = infixP (varP x1) (appendColon name) (varP x2)
          body = normalB $
            infixE (Just (varE x1)) (varE name) (Just (varE x2))
      clause [pat] body []


    appendF nm = mkName $ nameBase nm <> "F"
    appendColon nm = mkName $ nameBase nm <> ":"
    aux :: Con -> ReaderT Things Q Con
    aux (NormalC nm tys) = NormalC (appendF nm) <$>
      mapM (\(b, ty) -> (b,) <$> unfixTyQ ty) tys
    aux (RecC nm tys) = NormalC (appendF nm) <$>
      mapM (\(_, b, ty) -> (b,) <$> unfixTyQ ty) tys
    aux (InfixC (b1, ty1) nm (b2, ty2)) =
      InfixC <$> ((b1,) <$> unfixTyQ ty1)
             <*> pure (mkName $ nameBase nm <> ":")
             <*> ((b2,) <$> unfixTyQ ty2)

data Things =
  Things { mainTyName :: Name
         , tyVars :: [Name]
         , newVar :: Name
         }

unfixTyQ :: Type -> ReaderT Things Q Type
unfixTyQ = mapReaderT (maybe (fail err) pure) . unfixTy
  where err = "mkBaseFunctor: invalid type constructors"

unfixTy :: Type -> ReaderT Things Maybe Type
unfixTy ty = do
  Things name vars _ <- ask
  if isAppliedTy name vars ty
    then VarT <$> fmap newVar ask
    else case ty of
      AppT t1 t2 -> AppT <$> unfixTy t1 <*> unfixTy t2
      SigT t k -> SigT <$> unfixTy t <*> pure k
      VarT _ -> pure ty
      ConT _ -> pure ty
      InfixT t1 nm t2 -> InfixT <$> unfixTy t1 <*> pure nm <*> unfixTy t2
      ParensT t -> ParensT <$> unfixTy ty
      TupleT i -> pure (TupleT i)
      ArrowT -> pure ArrowT
      ListT -> pure ListT
      _ -> lift Nothing

isAppliedTy :: Name -> [Name] -> Type -> Bool
isAppliedTy nm [] (ConT nm') = nm == nm'
isAppliedTy nm vars (AppT ty (VarT nm')) =
  isAppliedTy nm (init vars) ty && last vars == nm'
isAppliedTy _ _ _ = False
