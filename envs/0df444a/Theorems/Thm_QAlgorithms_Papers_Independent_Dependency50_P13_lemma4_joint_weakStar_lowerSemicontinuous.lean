-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P13_lemma4_joint_weakStar_lowerSemicontinuous
-- name    : QAlgorithms.Papers.Independent.Dependency50.P13.lemma4_joint_weakStar_lowerSemicontinuous
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:10:12.550926+00:00
-- url     : https://prove2.me/theorems/a14edc00-8f2f-449c-9bae-d0ec3e099714
-- title:
--   Lemma 4: joint weak* lower semicontinuity of relative entropy
-- statement:
--   Let H be a nonzero separable complex Hilbert space. On all positive trace-class operators, including operators with arbitrary finite trace, the extended relative entropy in nats satisfies
--
--   $$ (X,Y)\longmapsto D(X\|Y)\quad\text{is lower semicontinuous for }\sigma(\mathcal T(H),\mathcal K(H))\times\sigma(\mathcal T(H),\mathcal K(H)). $$
--
--   Here D includes the trace correction Tr(Y-X), and support violations have value infinity. This supplies the compact-test lower semicontinuity needed for optimization over free states.
-- source:
--   Attainability and lower semi-continuity of the relative entropy of entanglement, and variations on the theme, arXiv:2105.08091v3, PDF p. 6, Lemma 4: joint weak* lower semicontinuity of relative entropy

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13

noncomputable section

open Filter MeasureTheory

open scoped ENNReal NNReal ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Dependency50.P13

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Lemma 4, arXiv:2105.08091v3, PDF p.6, (7).
Includes arbitrary positive trace-class operators and infinite divergence values. -/
theorem lemma4_joint_weakStar_lowerSemicontinuous [Nontrivial H] [TopologicalSpace.SeparableSpace H] {I : Type*} [Countable I]
    (b : HilbertBasis I ℂ H) :
    letI : TopologicalSpace (PositiveTraceClass H) :=
      @TopologicalSpace.induced (PositiveTraceClass H) (TraceClass H)
        (fun T => T.val) (weakStarTopology b)
    LowerSemicontinuous (fun p : PositiveTraceClass H × PositiveTraceClass H =>
      relativeEntropy p.1.val p.2.val) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P13

end
