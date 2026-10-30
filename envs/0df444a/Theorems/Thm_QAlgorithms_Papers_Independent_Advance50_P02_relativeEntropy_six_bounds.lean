-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P02_relativeEntropy_six_bounds
-- name    : QAlgorithms.Papers.Independent.Advance50.P02.relativeEntropy_six_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:22:13.370364+00:00
-- url     : https://prove2.me/theorems/641d8fa3-4333-4496-9f58-b0552029a721
-- title:
--   Six relative-entropy comparison inequalities
-- statement:
--   All Hilbert spaces are finite dimensional and complex; all logarithms are binary. Positive-operator inequalities use the identity when comparing with a scalar. Let $\rho$ be normalized, $\sigma\ge0$, $0<\varepsilon<1$, and $0<\delta<\varepsilon$. Let $\nu=\nu(\sigma)$, $\bar\rho=\mathcal E_\sigma(\rho)$, and let $P,Q$ be the Nussbaum–Szkola distributions from any full orthonormal spectral decompositions of this pair. Write $M=D_{\max}^{\sqrt{1-\varepsilon}}(\rho\Vert\sigma)$. All six inequalities hold:
--   $$\begin{aligned}
--   M&\ge D_s^{\varepsilon-\delta}(\rho\Vert\sigma)+2\log\delta-2-\log\varepsilon,\\
--   M&\le D_s^\varepsilon(\bar\rho\Vert\sigma)+\log\nu-\log(1-\varepsilon),\\
--   D_s^{\varepsilon-\delta}(\bar\rho\Vert\sigma)&\le D_s^\varepsilon(P\Vert Q)-\log\delta,\\
--   D_s^\varepsilon(\bar\rho\Vert\sigma)&\ge D_s^{\varepsilon-\delta}(P\Vert Q)+\log\delta-\log\nu,\\
--   M&\le D_h^\varepsilon(\rho\Vert\sigma)+\log\nu-\log(1-\varepsilon),\\
--   M&\ge D_h^{\varepsilon-\delta}(\rho\Vert\sigma)+3\log\delta-3\log3-\log\varepsilon.
--   \end{aligned}$$
--   These compare the one-shot quantities without a support restriction or an exact-mass cutoff assumption.
-- source:
--   A Hierarchy of Information Quantities for Finite Block Length Analysis of Quantum Tasks, arXiv:1208.1478v3, PDF p. 15, Proposition 13: six relative-entropy inequalities

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

/-- Proposition 13, PDF pp.15--17: six clauses, sqrt smoothing throughout. -/
theorem relativeEntropy_six_bounds (rho sigma : Mat I) (hrho : QAlgorithms.IsDensityMatrix rho)
    (hsigma : sigma.PosSemidef) (r : PositiveSpectralPresentation rho) (s : PositiveSpectralPresentation sigma)
    (e delta : ℝ) (he : 0 < e ∧ e < 1) (hdelta : 0 < delta ∧ delta < e) :
    spectrumEntropy (e-delta) rho sigma + (2*logTwo delta-2-logTwo e : ℝ) ≤
      smoothedMaxRelativeEntropy (Real.sqrt (1-e)) rho sigma ∧
    smoothedMaxRelativeEntropy (Real.sqrt (1-e)) rho sigma ≤ spectrumEntropy e (pinch sigma rho) sigma +
      (logTwo (distinctCount sigma)-logTwo (1-e) : ℝ) ∧
    spectrumEntropy (e-delta) (pinch sigma rho) sigma ≤
      classicalSpectrumDivergence e (nsProbability r s) (nsReferenceWeight r s) - (logTwo delta : ℝ) ∧
    classicalSpectrumDivergence (e-delta) (nsProbability r s) (nsReferenceWeight r s) +
      (logTwo delta-logTwo (distinctCount sigma) : ℝ) ≤ spectrumEntropy e (pinch sigma rho) sigma ∧
    smoothedMaxRelativeEntropy (Real.sqrt (1-e)) rho sigma ≤ extendedTestingDivergence e rho sigma +
      (logTwo (distinctCount sigma)-logTwo (1-e) : ℝ) ∧
    extendedTestingDivergence (e-delta) rho sigma + (3*logTwo delta-3*logTwo 3-logTwo e : ℝ) ≤
      smoothedMaxRelativeEntropy (Real.sqrt (1-e)) rho sigma := by sorry

end QAlgorithms.Papers.Independent.Advance50.P02

end
