-- Prove2me | Theorems.Thm_VectorSublattice_negPart_mem
-- name    : VectorSublattice.negPart_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:24:55.939577+00:00
-- url     : https://prove2.me/theorems/6265d237-e98b-4042-b915-eca1375e1451
-- title:
--   Vector Sublattice: neg Part mem
-- statement:
--   A vector sublattice is closed under the negative part.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Sublattice.lean#L166-L167
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Sublattice.lean#L166-L167

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

theorem VectorSublattice.negPart_mem {x : X} (hx : x ∈ Y) : x⁻ ∈ Y := by sorry
