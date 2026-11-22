-- Prove2me | Theorems.Thm_VecLatHom_map_abs
-- name    : VecLatHom.map_abs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:24:01.821532+00:00
-- url     : https://prove2.me/theorems/4ff70a29-45a2-4c7e-8fda-04091ef800f8
-- title:
--   Vec Lat Hom: map abs
-- statement:
--   A vector lattice homomorphism preserves absolute values.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Operators/Hom.lean#L103-L104
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Operators/Hom.lean#L103-L104

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

theorem VecLatHom.map_abs (f : VecLatHom X Y) (x : X) : f |x| = |f x| := by sorry
