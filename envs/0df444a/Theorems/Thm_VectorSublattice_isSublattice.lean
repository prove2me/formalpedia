-- Prove2me | Theorems.Thm_VectorSublattice_isSublattice
-- name    : VectorSublattice.isSublattice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:24:40.097805+00:00
-- url     : https://prove2.me/theorems/6ac0f2c7-2e0d-45ce-9177-adda3f9ccd6e
-- title:
--   Vector Sublattice: is Sublattice
-- statement:
--   The underlying set of a vector sublattice is an `IsSublattice`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Sublattice.lean#L174-L176
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Sublattice.lean#L174-L176

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

theorem VectorSublattice.isSublattice : IsSublattice (Y : Set X) := by sorry
