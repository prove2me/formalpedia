-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P18_entropy_strong_concavity
-- name    : QAlgorithms.Papers.Independent.Gap48.P18.entropy_strong_concavity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:34:51.68229+00:00
-- url     : https://prove2.me/theorems/c9175cbc-fac7-483b-af00-abe44f59e164
-- title:
--   Equation (5): quantitative entropy concavity
-- statement:
--   Let $\rho,\sigma$ be density states on a nonzero separable complex Hilbert space and $t\in[0,1]$. Entropy is measured in nats and may be infinite. Then
--
--   $$H(t\rho+(1-t)\sigma)\ge tH(\rho)+(1-t)H(\sigma)+\frac{t(1-t)}2\|\rho-\sigma\|_1^2.$$
--
--   The endpoint products $0\cdot\infty$ are zero. This is quantitative entropy concavity.
-- source:
--   Entropic characteristics of subsets of states, arXiv:quant-ph/0510073v2, PDF p. 6, Equation (5): quantitative entropy concavity

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P18

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal Topology Matrix.Norms.L2Operator

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState traceSize traceClosure IsTraceClassChannel productCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble HasFiniteSupport HasAverage averageCoefficients
   extendedEntropyNats extendedRelativeEntropyNats
   finiteEnsembleCapacity pureStates)

open QAlgorithms.Papers.Independent.Frontier18.P01 (traceFirst traceSecond)

namespace QAlgorithms.Papers.Independent.Gap48.P18

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Equation (5): quantitative entropy concavity, arXiv:quant-ph/0510073v2, PDF pp.6.
 -/
theorem entropy_strong_concavity {I : Type} [Countable I] [Nonempty I]
    (rho sigma : State I) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ENNReal.ofReal t * stateEntropyNats rho + ENNReal.ofReal (1 - t) * stateEntropyNats sigma +
        ENNReal.ofReal (t * (1 - t) / 2) * distanceSquared sigma rho ≤
      extendedEntropyNats ((t : ℂ) • rho.coefficients +
        ((1 - t : ℝ) : ℂ) • sigma.coefficients) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P18

end
