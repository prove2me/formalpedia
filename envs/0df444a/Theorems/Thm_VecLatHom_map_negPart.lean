-- Prove2me | Theorems.Thm_VecLatHom_map_negPart
-- name    : VecLatHom.map_negPart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:24:13.769022+00:00
-- url     : https://prove2.me/theorems/d0fa6c25-a923-4b39-800e-371ec4a55bde
-- title:
--   Vec Lat Hom: map neg Part
-- statement:
--   A vector lattice homomorphism preserves negative parts: `f x⁻ = (f x)⁻`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Operators/Hom.lean#L128-L129
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Operators/Hom.lean#L128-L129

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

theorem VecLatHom.map_negPart (f : VecLatHom X Y) (x : X) : f x⁻ = (f x)⁻ := by sorry
