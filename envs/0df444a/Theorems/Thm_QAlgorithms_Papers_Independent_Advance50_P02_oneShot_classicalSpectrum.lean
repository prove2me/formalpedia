-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P02_oneShot_classicalSpectrum
-- name    : QAlgorithms.Papers.Independent.Advance50.P02.oneShot_classicalSpectrum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:22:53.460799+00:00
-- url     : https://prove2.me/theorems/ac3b30fc-ee7a-43d2-9822-9023ccee234e
-- title:
--   One-shot/classical-spectrum comparison
-- statement:
--   All Hilbert spaces are finite dimensional and complex; all logarithms are binary. Positive-operator inequalities use the identity when comparing with a scalar. Let $\rho$ be normalized, $\sigma\ge0$, $0<\varepsilon<1$, and $0<\delta<\min\{\varepsilon,1-\varepsilon\}$. Let $P,Q$ be the pair's Nussbaum–Szkola distributions. For invertible $\sigma$, put $\lambda=\log\lambda_{\max}-\log\lambda_{\min}$ and $\theta=\min\{2\max(1,\lceil\lambda\rceil),\nu(\sigma)\}$; for singular $\sigma$, use $\theta=\nu(\sigma)$. Then
--   $$\begin{aligned}
--   D_h^\varepsilon&\le D_s^{\varepsilon+\delta}(P\Vert Q)+\log\frac{2^8(\varepsilon+\delta)\theta}{\delta^4(1-\varepsilon-\delta)},\\
--   D_h^\varepsilon&\ge D_s^{\varepsilon-\delta}(P\Vert Q)-\log\theta+\log\delta,\\
--   D_{\max}^{\sqrt{1-\varepsilon}}&\le D_s^{\varepsilon+\delta}(P\Vert Q)+\log\theta-\log(\delta(1-\varepsilon)),\\
--   D_{\max}^{\sqrt{1-\varepsilon}}&\ge D_s^{\varepsilon-\delta}(P\Vert Q)-\log(3^3\varepsilon\theta)+\log\delta^3.
--   \end{aligned}$$
--   The quantum quantities on the left have arguments $(\rho\Vert\sigma)$. These bounds preserve flat spectra by the positive-bin correction described in the audit.
-- source:
--   A Hierarchy of Information Quantities for Finite Block Length Analysis of Quantum Tasks, arXiv:1208.1478v3, PDF p. 17, Theorem 14: one-shot/classical-spectrum comparison

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P02

noncomputable section

open Filter

open scoped BigOperators Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Advance50.P02

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P63
  (Mat tensorPower logTwo normalQuantile testingBeta)

open QAlgorithms.Papers.Independent.Information100.P71 (SupportIncluded supportPower)

open QAlgorithms (effectProb)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P30 (tensorMap)

open QAlgorithms.Papers.Independent.Information100.P67 (purifiedDistance)

open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)

open QAlgorithms.Papers.Independent.Dependency50.P28 (pinch)

variable {I J A B X Z : Type} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype X] [DecidableEq X]
  [Fintype Z] [DecidableEq Z]

/-- Theorem 14, PDF pp.17--18: four bounds with the positive-bin repair of positiveSpectralFactor.
Printed/changed/why is recorded in MODERATION_NOTES.md. Source correction. Printed: p.17 defines theta=min(2 ceil(lambda),nu), zero for flat spectra.
Changed: For positive definite sigma use theta=min(2 max(1,ceil(lambda)),nu); singular sigma uses the independently proved nu branch.
Why: p.18 requires a positive integer bin count. Flat spectra have nu=1 and corrected theta=1. The nu proof covers singular comparisons without evaluating log(0); all four constants and conclusions are retained. -/
theorem oneShot_classicalSpectrum (rho sigma : Mat I) (hrho : QAlgorithms.IsDensityMatrix rho)
    (hsigma : sigma.PosSemidef) (r : PositiveSpectralPresentation rho) (s : PositiveSpectralPresentation sigma)
    (e delta : ℝ) (he : 0 < e ∧ e < 1)
    (hdelta : 0 < delta ∧ delta < min e (1-e)) :
    extendedTestingDivergence e rho sigma ≤ classicalSpectrumDivergence (e+delta) (nsProbability r s) (nsReferenceWeight r s) +
      (logTwo ((2:ℝ)^8*(e+delta)*positiveSpectralFactor sigma / (delta^4*(1-e-delta))) : ℝ) ∧
    classicalSpectrumDivergence (e-delta) (nsProbability r s) (nsReferenceWeight r s) - (logTwo (positiveSpectralFactor sigma) : ℝ) +
      (logTwo delta : ℝ) ≤ extendedTestingDivergence e rho sigma ∧
    smoothedMaxRelativeEntropy (Real.sqrt (1-e)) rho sigma ≤ classicalSpectrumDivergence (e+delta) (nsProbability r s) (nsReferenceWeight r s) +
      (logTwo (positiveSpectralFactor sigma)-logTwo (delta*(1-e)) : ℝ) ∧
    classicalSpectrumDivergence (e-delta) (nsProbability r s) (nsReferenceWeight r s) - (logTwo ((3:ℝ)^3*e*positiveSpectralFactor sigma) : ℝ) +
      (logTwo (delta^3) : ℝ) ≤ smoothedMaxRelativeEntropy (Real.sqrt (1-e)) rho sigma := by sorry

end QAlgorithms.Papers.Independent.Advance50.P02

end
