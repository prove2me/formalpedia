-- Prove2me | Theorems.Thm_VectorSublattice_mem_bot
-- name    : VectorSublattice.mem_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:24:31.649798+00:00
-- url     : https://prove2.me/theorems/3ee89dc8-ea5a-41df-94bc-d604deaba7bc
-- title:
--   Vector Sublattice: mem bot
-- statement:
--   An element of `⊥` is zero.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Sublattice.lean#L294-L295
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Sublattice.lean#L294-L295

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

theorem VectorSublattice.mem_bot {x : X} : x ∈ (⊥ : VectorSublattice X) ↔ x = 0 := by sorry
