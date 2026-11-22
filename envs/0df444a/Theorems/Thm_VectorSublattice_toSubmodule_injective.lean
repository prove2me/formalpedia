-- Prove2me | Theorems.Thm_VectorSublattice_toSubmodule_injective
-- name    : VectorSublattice.toSubmodule_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:24:37.200625+00:00
-- url     : https://prove2.me/theorems/2777c3a6-afa5-4464-a625-995a1c89b2a8
-- title:
--   Vector Sublattice: to Submodule injective
-- statement:
--   The coercion to `Submodule ℝ X` is injective.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Sublattice.lean#L210-L214
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Sublattice.lean#L210-L214

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Definitions.Def_LeanPool_OrderClosures_BanLat_LLexpr
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.Order.Sublattice
public import Mathlib.Order.SupClosed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Sublattice
set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
open VectorSublattice
variable (Y : VectorSublattice X)

theorem VectorSublattice.toSubmodule_injective :
    Function.Injective
      (toSubmodule : VectorSublattice X → Submodule ℝ X) := by sorry
