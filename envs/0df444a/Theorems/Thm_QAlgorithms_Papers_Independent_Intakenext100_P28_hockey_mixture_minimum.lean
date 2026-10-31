-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_hockey_mixture_minimum
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.hockey_mixture_minimum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:47:12.845847+00:00
-- url     : https://prove2.me/theorems/0db48c31-d863-4809-a209-09a20fd880da
-- title:
--   Corollary 5: E_gamma<=min_(0<=lambda<=1)[lambda TV/2+c_gamma D((1-lambda)P+lambda Q||Q)]
-- statement:
--   For $P\ll Q$ and $\gamma>1$,
--
--   $$E_\gamma(P\|Q)\le\min_{0\le\lambda\le1}
--   \left\{\frac\lambda2|P-Q|+c_\gamma D((1-\lambda)P+\lambda Q\|Q)\right\}.$$
--
--   The statement includes existence of a minimizing mixture parameter in the compact interval. Extended KL permits infinite endpoint values; the minimum remains attained.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 64, Corollary 5

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Corollary 5: E_gamma<=min_(0<=lambda<=1)[lambda TV/2+c_gamma D((1-lambda)P+lambda Q||Q)]. Sason--Verdu, arXiv:1508.00335v7, PDF p.64.  -/
theorem hockey_mixture_minimum
    (b : LogBase) {A : Type u} [MeasurableSpace A] (P Q : Measure A)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hPQ : P ≪ Q) (g : ℝ) (hg : 1 < g) :
    ∃ t : ℝ, t ∈ Icc 0 1 ∧
      IsLeast {z : ℝ≥0∞ | ∃ s : ℝ, s ∈ Icc 0 1 ∧
        z = ENNReal.ofReal (s / 2) * fullVariation P Q +
          ENNReal.ofReal (hockeyKLConstant b g) * kl b (probabilityMixture P Q s) Q}
        (ENNReal.ofReal (t / 2) * fullVariation P Q + ENNReal.ofReal (hockeyKLConstant b g) * kl b (probabilityMixture P Q t) Q) ∧
      hockey g P Q ≤ ENNReal.ofReal (t / 2) * fullVariation P Q +
        ENNReal.ofReal (hockeyKLConstant b g) * kl b (probabilityMixture P Q t) Q := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
