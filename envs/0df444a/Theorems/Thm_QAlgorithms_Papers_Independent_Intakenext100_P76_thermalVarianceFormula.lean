-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P76_thermalVarianceFormula
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P76.thermalVarianceFormula
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:50:38.663129+00:00
-- url     : https://prove2.me/theorems/18551747-fe26-483d-bf2f-77cd2008b5d2
-- title:
--   Thermal spectral entropy variance, including vacuum
-- statement:
--   For $x\ge0$, let $\theta(x)$ be the full number-diagonal thermal state with eigenvalues $p_x(k)=x^k/(x+1)^{k+1}$ for $k=0,1,\ldots$. Compute $H(\theta(x))=\sum_kp_x(k)[-\log_2p_x(k)]$ and its variance independently as the second central moment of this spectral self-information, with zero-weight terms contributing zero. Both moment series converge, and
--
--   $$
--   V(\theta(x))=v(x),\qquad
--   v(x)=x(x+1)[\log_2(x+1)-\log_2x]^2\quad(x>0),\qquad v(0)=0.
--   $$
--
--   At $x=0$, both entropy and variance are zero. This identifies the bosonic dispersion with the actual spectral variance rather than defining the variance by the claimed answer.
-- source:
--   Second-order coding rates for pure-loss bosonic channels, arXiv:1408.5328v3, PDF p. 10, (6.7), Appendix A (A.1)–(A.7), PDF p.15

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P76

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P76

open MeasureTheory Filter

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo normalCDF normalQuantile)

open QAlgorithms.Papers.Independent.Information100.P54 (thermalEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)

open QAlgorithms.Papers.Independent.Next46.P32 (PositiveKernel)

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.10, (6.7), Appendix A, PDF p.15, (A.1)–(A.7): the independently
computed thermal spectral variance equals the stated dispersion. Vacuum has
zero entropy and variance. Summability prevents total-tsum default values. -/
theorem thermalVarianceFormula (x : ℝ) (hx : 0 ≤ x) :
    Summable (fun k => thermalPhotonProbability x k * (-logTwo (thermalPhotonProbability x k))) ∧
    Summable (fun k => thermalPhotonProbability x k *
      (-logTwo (thermalPhotonProbability x k) - selfInformationMean (thermalPhotonProbability x)) ^ 2) ∧
    selfInformationVariance (thermalPhotonProbability x) = thermalDispersion x ∧
    (x = 0 → selfInformationMean (thermalPhotonProbability x) = 0 ∧
      selfInformationVariance (thermalPhotonProbability x) = 0) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P76

end
