-- Prove2me | Theorems.Thm_VectorSublattice_posPart_mem
-- name    : VectorSublattice.posPart_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:24:59.165861+00:00
-- url     : https://prove2.me/theorems/71fc13c2-0622-429b-b273-be395b5cacdc
-- title:
--   Vector Sublattice: pos Part mem
-- statement:
--   A vector sublattice is closed under the positive part.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Sublattice.lean#L162-L163
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Sublattice.lean#L162-L163

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

theorem VectorSublattice.posPart_mem {x : X} (hx : x ∈ Y) : x⁺ ∈ Y := by sorry
