-- Prove2me | Theorems.Thm_VecLatHom_map_disjoint
-- name    : VecLatHom.map_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:24:16.377728+00:00
-- url     : https://prove2.me/theorems/a1838469-4955-49f2-a250-00372bb58d06
-- title:
--   Vec Lat Hom: map disjoint
-- statement:
--   A vector lattice homomorphism preserves disjointness: `x ⊓ y = 0 → f x ⊓ f y = 0`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Operators/Hom.lean#L132-L133
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Operators/Hom.lean#L132-L133

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

theorem VecLatHom.map_disjoint (f : VecLatHom X Y) {x y : X} (h : x ⊓ y = 0) : f x ⊓ f y = 0 := by sorry
