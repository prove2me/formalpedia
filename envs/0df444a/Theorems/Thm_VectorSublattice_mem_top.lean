-- Prove2me | Theorems.Thm_VectorSublattice_mem_top
-- name    : VectorSublattice.mem_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:24:29.265108+00:00
-- url     : https://prove2.me/theorems/2728d968-e4b4-4e84-ad6e-9aa70b7fdc06
-- title:
--   Vector Sublattice: mem top
-- statement:
--   Every element belongs to `⊤`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Sublattice.lean#L280-L281
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Sublattice.lean#L280-L281

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

theorem VectorSublattice.mem_top {x : X} : x ∈ (⊤ : VectorSublattice X) := by sorry
