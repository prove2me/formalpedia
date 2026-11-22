-- Prove2me | Theorems.Thm_VecLatHom_symm_apply
-- name    : VecLatHom.symm_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:24:04.794989+00:00
-- url     : https://prove2.me/theorems/3d5f17b0-9319-42b5-8bc8-41dcd98a0ed0
-- title:
--   Vec Lat Hom: symm apply
-- statement:
--   The inverse bijection from `symm`: `(f.symm h) y = x ↔ y = f x`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Operators/Hom.lean#L222-L226
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Operators/Hom.lean#L222-L226

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

theorem VecLatHom.symm_apply (f : VecLatHom X Y) (h : Function.Bijective f)
  (x : X) (y : Y) : (f.symm h) y = x ↔ y = f x := by sorry
