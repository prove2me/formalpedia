-- Prove2me | Theorems.Thm_VecLatHom_map_posPart
-- name    : VecLatHom.map_posPart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:24:17.218358+00:00
-- url     : https://prove2.me/theorems/21ac507f-d5f2-45d9-94aa-af20d137fa86
-- title:
--   Vec Lat Hom: map pos Part
-- statement:
--   A vector lattice homomorphism preserves positive parts: `f x⁺ = (f x)⁺`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Operators/Hom.lean#L124-L125
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Operators/Hom.lean#L124-L125

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

theorem VecLatHom.map_posPart (f : VecLatHom X Y) (x : X) : f x⁺ = (f x)⁺ := by sorry
