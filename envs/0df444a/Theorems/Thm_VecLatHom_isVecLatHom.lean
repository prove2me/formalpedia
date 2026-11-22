-- Prove2me | Theorems.Thm_VecLatHom_isVecLatHom
-- name    : VecLatHom.isVecLatHom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:24:30.800252+00:00
-- url     : https://prove2.me/theorems/ca9bb878-cfbf-43d3-bc22-71e7d63df6e3
-- title:
--   Vec Lat Hom: is Vec Lat Hom
-- statement:
--   Every `VecLatHom` satisfies the `IsVecLatHom` predicate.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Operators/Hom.lean#L66-L70
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Operators/Hom.lean#L66-L70

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Operators_Positive
public import Definitions.Def_LeanPool_OrderClosures_BanLat_LLexpr
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Operators_Hom
set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} {Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  [Lattice X] [Lattice Y] [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
  [VectorLattice X] [VectorLattice Y]
open VecLatHom

theorem VecLatHom.isVecLatHom (f : VecLatHom X Y) : IsVecLatHom f := by sorry
