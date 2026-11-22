-- Prove2me | Theorems.Thm_VectorSublattice_coe_toSubmodule
-- name    : VectorSublattice.coe_toSubmodule
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:24:26.28482+00:00
-- url     : https://prove2.me/theorems/50889bfc-db52-4cab-b77c-c62738be9d36
-- title:
--   Vector Sublattice: coe to Submodule
-- statement:
--   A vector sublattice and its underlying submodule have the same carrier.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Sublattice.lean#L218-L218
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Sublattice.lean#L218-L218

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

theorem VectorSublattice.coe_toSubmodule : (Y.toSubmodule : Set X) = (Y : Set X) := by sorry

attribute [defeq] VectorSublattice.coe_toSubmodule
