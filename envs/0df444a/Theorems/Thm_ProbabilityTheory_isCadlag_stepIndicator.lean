-- Prove2me | Theorems.Thm_ProbabilityTheory_isCadlag_stepIndicator
-- name    : ProbabilityTheory.isCadlag_stepIndicator
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:07:45.857093+00:00
-- url     : https://prove2.me/theorems/d8596e2a-c4a5-4b16-b141-f270c97f7ca3
-- title:
--   LeanLevy: ProbabilityTheory.isCadlag_stepIndicator
-- statement:
--   The right-continuous real step indicator has right-continuous paths with left limits. Pinned source theorem, with its original proof previously compiled; awaiting remote Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/Cadlag.lean#L168

import Definitions.Def_LeanLevy_Processes_Cadlag
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Order.Preorder.Finite
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Algebra.Monoid

theorem ProbabilityTheory.isCadlag_stepIndicator : ∀ {c y : Real},
  @ProbabilityTheory.IsCadlag Real Real
    (@UniformSpace.toTopologicalSpace Real (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))
    (@UniformSpace.toTopologicalSpace Real (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))
    Real.instPreorder fun t =>
    @ite Real (@LE.le Real Real.instLE c t) (c.decidableLE t) y
      (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) := by sorry
