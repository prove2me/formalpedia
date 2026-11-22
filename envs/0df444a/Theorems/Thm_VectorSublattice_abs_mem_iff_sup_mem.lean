-- Prove2me | Theorems.Thm_VectorSublattice_abs_mem_iff_sup_mem
-- name    : VectorSublattice.abs_mem_iff_sup_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:24:52.981362+00:00
-- url     : https://prove2.me/theorems/f28a557f-ec06-42bd-8e4f-a67ed0a6e2b6
-- title:
--   Vector Sublattice: abs mem iff sup mem
-- statement:
--   A submodule is a vector sublattice iff it is closed under absolute value.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Sublattice.lean#L198-L205
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Sublattice.lean#L198-L205

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

theorem VectorSublattice.abs_mem_iff_sup_mem (M : Submodule ℝ X) :
    (∀ x : X, x ∈ M → |x| ∈ M) ↔
      ∀ x y : X, x ∈ M → y ∈ M → x ⊔ y ∈ M := by sorry
