-- Prove2me | Theorems.Thm_Positive_le_def
-- name    : Positive.le_def
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:14:09.010805+00:00
-- url     : https://prove2.me/theorems/246f11e4-acb6-41fe-bb05-0d9f4226501e
-- title:
--   Positive: le def
-- statement:
--   The Positive construction uses the le def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Operators/Positive.lean#L70-L70
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Operators/Positive.lean#L70-L70

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

theorem Positive.le_def {T S : X →ₗ[ℝ] Y} : T ≤ S ↔ Positive (S - T) := by sorry
