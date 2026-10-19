-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P10_stableSimplexCounterexample
-- name    : QAlgorithms.Papers.Independent.Frontier18.P10.stableSimplexCounterexample
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:18:23.814235+00:00
-- url     : https://prove2.me/theorems/44144632-df25-45d3-b79b-b7e8306fd474
-- title:
--   Proposition 18: stable counterexample to the five-way equivalence
-- statement:
--   For every finite real $p>1$, the subprobability simplex $\Delta_p=\{x\in\ell^p(\mathbb N):x_i\ge0,\ \sum_i x_i\le1\}$ is pointwise $\mu$-compact and satisfies Theorem 1(i) and (ii), but
--   $$\neg\mathrm{(iii)},\qquad\neg\mathrm{(iv)},\qquad\neg\mathrm{(v)}.$$
--   For $p=1$, $\Delta_1=A_1$ is $\mu$-compact and satisfies all five properties. Property (iii) uses probabilities on the closure of the extreme boundary.
--
--   The example preserves the distinction between stability and the full five-way equivalence without µ-compactness.
-- source:
--   Generalized compactness in linear spaces and its applications, arXiv:1002.3610v3, PDF p. 16, Proposition 18: stable counterexample to the five-way equivalence

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P10

noncomputable section

open Set Filter MeasureTheory TopologicalSpace

open scoped Topology ENNReal BigOperators

universe u v w

namespace QAlgorithms.Papers.Independent.Frontier18.P10

open QAlgorithms.Papers.Independent.Dependency50.P25

attribute [local instance] QAlgorithms.Papers.Independent.Frontier18.P10.paperMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Frontier18.P10.paperBorel

section LpResults

/-- Proposition 18, PDF pp.16–18: all three failures (iii),(iv),(v), both
positive properties (i),(ii), pointwise compactness, and the p=1 contrast. -/
theorem stableSimplexCounterexample (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : 1 < p) (hfinite : p < ⊤) :
    (PointwiseMuCompact (subprobabilitySimplex p) ∧
      StableConvexSet (subprobabilitySimplex p) ∧
      BarycenterOpen (subprobabilitySimplex p) (subprobabilitySimplex p) ∧
      ¬ BarycenterOpen (subprobabilitySimplex p)
        (closure ((subprobabilitySimplex p).extremePoints ℝ)) ∧
      ¬ StrongCEProperty (subprobabilitySimplex p) ∧
      ¬ CEProperty (subprobabilitySimplex p)) ∧
    (subprobabilitySimplex 1 = positiveLpUnitPart 1 ∧
      MuCompact (subprobabilitySimplex 1) ∧ StableConvexSet (subprobabilitySimplex 1) ∧
      BarycenterOpen (subprobabilitySimplex 1) (subprobabilitySimplex 1) ∧
      BarycenterOpen (subprobabilitySimplex 1)
        (closure ((subprobabilitySimplex 1).extremePoints ℝ)) ∧
      StrongCEProperty (subprobabilitySimplex 1) ∧ CEProperty (subprobabilitySimplex 1)) := by sorry

end LpResults

end QAlgorithms.Papers.Independent.Frontier18.P10

end
