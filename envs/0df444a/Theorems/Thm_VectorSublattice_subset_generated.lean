-- Prove2me | Theorems.Thm_VectorSublattice_subset_generated
-- name    : VectorSublattice.subset_generated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:24:11.454803+00:00
-- url     : https://prove2.me/theorems/eec9a074-cb90-4e9d-80f9-c9ce3554838d
-- title:
--   Vector Sublattice: subset generated
-- statement:
--   The generating set is contained in the vector sublattice it generates.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Sublattice.lean#L320-L324
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Sublattice.lean#L320-L324

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

theorem VectorSublattice.subset_generated (s : Set X) : s ⊆ (generated s : Set X) := by sorry
