-- Prove2me | Theorems.Thm_VecLatHom_le_of_map_le
-- name    : VecLatHom.le_of_map_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:24:19.514435+00:00
-- url     : https://prove2.me/theorems/ab261895-0059-4c55-bef9-735cd28bfb25
-- title:
--   Vec Lat Hom: le of map le
-- statement:
--   An injective vector lattice homomorphism reflects the order: if `f a ≤ f b` then
--   `a ≤ b`. Together with `monotone`, an injective vector lattice homomorphism is an order
--   embedding.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Operators/Hom.lean#L119-L121
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Operators/Hom.lean#L119-L121

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

theorem VecLatHom.le_of_map_le (f : VecLatHom X Y) (hf : Function.Injective f) {a b : X}
    (hab : f a ≤ f b) : a ≤ b := by sorry
