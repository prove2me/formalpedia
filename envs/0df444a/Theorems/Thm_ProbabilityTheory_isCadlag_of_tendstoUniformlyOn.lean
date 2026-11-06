-- Prove2me | Theorems.Thm_ProbabilityTheory_isCadlag_of_tendstoUniformlyOn
-- name    : ProbabilityTheory.isCadlag_of_tendstoUniformlyOn
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:07:56.008601+00:00
-- url     : https://prove2.me/theorems/bba2663f-46c7-4fbd-9ec7-93504ca52638
-- title:
--   LeanLevy: ProbabilityTheory.isCadlag_of_tendstoUniformlyOn
-- statement:
--   Locally uniform convergence on left-bounded intervals preserves the càdlàg property of real-valued functions. Pinned source theorem, with its original proof previously compiled; awaiting remote Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/Cadlag.lean#L198

import Definitions.Def_LeanLevy_Processes_Cadlag
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Order.Preorder.Finite
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Algebra.Monoid

theorem ProbabilityTheory.isCadlag_of_tendstoUniformlyOn : ∀ {F : Nat → Real → Real} {f : Real → Real},
  (∀ (n : Nat),
      @ProbabilityTheory.IsCadlag Real Real
        (@UniformSpace.toTopologicalSpace Real (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))
        (@UniformSpace.toTopologicalSpace Real (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))
        Real.instPreorder (F n)) →
    (∀ (T : Real),
        @TendstoUniformlyOn Real Real Nat (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace) F f
          (@Filter.atTop Nat Nat.instPreorder) (@Set.Iic Real Real.instPreorder T)) →
      @ProbabilityTheory.IsCadlag Real Real
        (@UniformSpace.toTopologicalSpace Real (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))
        (@UniformSpace.toTopologicalSpace Real (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))
        Real.instPreorder f := by sorry
