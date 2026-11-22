-- Prove2me | Theorems.Thm_VectorSublattice_coe_toPointedCone
-- name    : VectorSublattice.coe_toPointedCone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:24:50.799142+00:00
-- url     : https://prove2.me/theorems/fd215d92-bbd3-487a-aeb4-02208b15e7c7
-- title:
--   Vector Sublattice: coe to Pointed Cone
-- statement:
--   The Vector Sublattice construction uses the coe to Pointed Cone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Sublattice.lean#L231-L232
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Sublattice.lean#L231-L232

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

theorem VectorSublattice.coe_toPointedCone (Y : VectorSublattice X) :
    ((Y : PointedCone ℝ X) : Set X) = (Y : Set X) := by sorry
