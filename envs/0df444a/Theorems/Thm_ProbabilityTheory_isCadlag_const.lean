-- Prove2me | Theorems.Thm_ProbabilityTheory_isCadlag_const
-- name    : ProbabilityTheory.isCadlag_const
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:56:32.038152+00:00
-- url     : https://prove2.me/theorems/f9894139-8d1d-45d5-8a65-ee832a7cc600
-- title:
--   LeanLevy: ProbabilityTheory.isCadlag_const
-- statement:
--   Constant functions are càdlàg. Exact extracted Lean theorem type; proof pending Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/Cadlag.lean#L62

import Definitions.Def_LeanLevy_Processes_Cadlag
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Order.Preorder.Finite
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Algebra.Monoid

universe u_1 u_2
theorem ProbabilityTheory.isCadlag_const : ∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [inst_2 : Preorder α] {c : β},
  @ProbabilityTheory.IsCadlag α β inst inst_1 inst_2 fun x => c := by sorry
