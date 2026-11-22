-- Prove2me | Theorems.Thm_VecLatHom_map_nonneg
-- name    : VecLatHom.map_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:24:22.566271+00:00
-- url     : https://prove2.me/theorems/e5137a00-4834-483c-b2ed-520362905f2c
-- title:
--   Vec Lat Hom: map nonneg
-- statement:
--   A vector lattice homomorphism maps nonneg elements to nonneg elements.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Operators/Hom.lean#L113-L114
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Operators/Hom.lean#L113-L114

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

theorem VecLatHom.map_nonneg (f : VecLatHom X Y) {x : X} (hx : 0 ≤ x) : 0 ≤ f x := by sorry
