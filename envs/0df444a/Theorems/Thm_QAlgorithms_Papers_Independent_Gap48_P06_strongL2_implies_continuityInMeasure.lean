-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P06_strongL2_implies_continuityInMeasure
-- name    : QAlgorithms.Papers.Independent.Gap48.P06.strongL2_implies_continuityInMeasure
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:07:30.621784+00:00
-- url     : https://prove2.me/theorems/294f59f0-f238-431c-9492-626f51e627e7
-- title:
--   Strong L2 continuity implies continuity in measure
-- statement:
--   Let $S$ be a topological semigroup and $(X,\Sigma,\mu)$ a measure space. Let $P_s$ be a positivity-preserving semigroup on $L^\infty(X,\mu)$ whose compatible bounded linear action on $L^2(X,\mu)$ is strongly continuous. Real or complex scalar-valued functions are allowed, with positivity meaning real nonnegative values. Then, for every $f\in L^2(X,\mu)$, every $s_0\in S$ and every $\varepsilon>0$,
--
--   $$\lim_{s\to s_0}\mu\{x:|P_sf(x)-P_{s_0}f(x)|\ge\varepsilon\}=0.$$
--
--   Compatibility means equality almost everywhere of the two actions on the intersection of their domains. Event measures take values in $[0,\infty]$, so no finite-total-mass assumption is needed. This result passes from Hilbert-space continuity to the continuity used for stochastic processes.
-- source:
--   Reflection Positive Stochastic Processes Indexed by Lie Groups, arXiv:1510.07445v3, PDF p. 43, Lemma A.1

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P06

noncomputable section

open MeasureTheory ProbabilityTheory Filter

open scoped Topology ENNReal NNReal

namespace QAlgorithms.Papers.Independent.Gap48.P06

/-- Lemma A.1, PDF p.43: strong L2 continuity implies continuity in measure,
for L2 vectors, with the L-infinity action compatible on the intersection.
The page switches mu/nu; one fixed measure is used, as in its L2 estimate. -/
theorem strongL2_implies_continuityInMeasure
    {S X K : Type*} [Semigroup S] [TopologicalSpace S] [ContinuousMul S]
    [MeasurableSpace X] [RCLike K] (mu : Measure X)
    (P : CompatiblePositiveSemigroup S X K mu)
    (hstrong : ∀ f, Continuous (fun s => P.onL2 s f)) :
    ∀ (f : Lp K 2 mu) (s0 : S),
      ContinuousInMeasureAt mu (fun s x => (P.onL2 s f) x) s0 := by sorry

end QAlgorithms.Papers.Independent.Gap48.P06

end
