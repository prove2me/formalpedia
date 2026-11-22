-- Prove2me | Theorems.Thm_Positive_continuous
-- name    : Positive.continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:25.328554+00:00
-- url     : https://prove2.me/theorems/1a13ef50-928b-4643-a96f-158b753e2de1
-- title:
--   Positive: continuous
-- statement:
--   Every positive linear operator from a Banach lattice to a normed vector lattice
--   is continuous.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Operators/Positive.lean#L316-L342
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Operators/Positive.lean#L316-L342

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
variable {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [Lattice X] [Lattice Y] [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
  [BanachLattice X] [NormedVectorLattice Y]

theorem Positive.continuous {f : X →ₗ[ℝ] Y} (hf : Positive f) : Continuous f := by sorry
