-- Prove2me | Theorems.Thm_Positive_monotone_iff
-- name    : Positive.monotone_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:49.514812+00:00
-- url     : https://prove2.me/theorems/cb7ddfc7-2edd-47cb-b019-fc93b3a7c165
-- title:
--   Positive: monotone iff
-- statement:
--   For a linear map between vector lattices, monotonicity and positivity are equivalent.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Operators/Positive.lean#L45-L51
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Operators/Positive.lean#L45-L51

module
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Mathlib.Algebra.Order.Module.Basic
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Module.Equiv
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Operators_Positive
set_option autoImplicit true
@[expose] public section
public section
variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] [Lattice X] [Lattice Y]
  [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y] [VectorLattice X] [VectorLattice Y]
open Positive

theorem Positive.monotone_iff {f : X →ₗ[ℝ] Y} : Monotone f ↔ Positive f := by sorry
