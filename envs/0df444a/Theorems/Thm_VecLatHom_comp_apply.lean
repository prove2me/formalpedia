-- Prove2me | Theorems.Thm_VecLatHom_comp_apply
-- name    : VecLatHom.comp_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:24:17.58405+00:00
-- url     : https://prove2.me/theorems/aaccc0a4-d5e9-494c-996f-2525f884a128
-- title:
--   Vec Lat Hom: comp apply
-- statement:
--   Evaluation of a composed `VecLatHom`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Operators/Hom.lean#L173-L179
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Operators/Hom.lean#L173-L179

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

theorem VecLatHom.comp_apply {Z : Type*} [AddCommGroup Z] [Lattice Z]
  [IsOrderedAddMonoid Z] [VectorLattice Z] (g : VecLatHom Y Z)
  (f : VecLatHom X Y) (x : X) : g.comp f x = g (f x) := by sorry
