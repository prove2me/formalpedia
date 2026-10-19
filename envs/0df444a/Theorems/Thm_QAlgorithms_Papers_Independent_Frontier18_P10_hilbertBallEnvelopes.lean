-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P10_hilbertBallEnvelopes
-- name    : QAlgorithms.Papers.Independent.Frontier18.P10.hilbertBallEnvelopes
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:12:45.897726+00:00
-- url     : https://prove2.me/theorems/d1785e9b-c606-4d10-9dbf-c66d4642841b
-- title:
--   Remark 3: bounded continuous envelopes on a Hilbert ball
-- statement:
--   Let $B$ be the closed unit ball of a complete separable real Hilbert space $H$. Every bounded continuous real $f$ on $B$ has continuous convex hull:
--   $$\operatorname{co}f\in C(B).$$
--   If $H$ is infinite-dimensional, $B$ is not pointwise $\mu$-compact.
--
--   Continuity applies also in finite dimension; only the noncompactness clause needs infinite dimension.
-- source:
--   Generalized compactness in linear spaces and its applications, arXiv:1002.3610v3, PDF p. 9, Remark 3: bounded continuous envelopes on a Hilbert ball

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P10

noncomputable section

open Set Filter MeasureTheory TopologicalSpace

open scoped Topology ENNReal BigOperators

universe u v w

namespace QAlgorithms.Papers.Independent.Frontier18.P10

open QAlgorithms.Papers.Independent.Dependency50.P25

attribute [local instance] QAlgorithms.Papers.Independent.Frontier18.P10.paperMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Frontier18.P10.paperBorel

section HilbertResults

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [hcomplete : CompleteSpace H]

include hcomplete

/-- Remark 3, PDF p.9: bounded continuous convex hulls on a separable
Hilbert ball are continuous. Printed: non-pointwise-compactness without a
dimension restriction. Changed: that clause requires infinite dimension,
because finite-dimensional balls are compact. -/
theorem hilbertBallEnvelopes [SeparableSpace H] :
    StrongCEProperty (Metric.closedBall (0 : H) 1) ∧
    (¬ FiniteDimensional ℝ H →
      ¬ PointwiseMuCompact (Metric.closedBall (0 : H) 1)) := by sorry

end HilbertResults

end QAlgorithms.Papers.Independent.Frontier18.P10

end
