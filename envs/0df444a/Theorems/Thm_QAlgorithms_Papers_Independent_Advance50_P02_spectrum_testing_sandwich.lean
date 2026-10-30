-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P02_spectrum_testing_sandwich
-- name    : QAlgorithms.Papers.Independent.Advance50.P02.spectrum_testing_sandwich
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:21:11.515145+00:00
-- url     : https://prove2.me/theorems/9423a7e5-f3c1-4a5e-b939-5d33728d2244
-- title:
--   Information-spectrum/testing sandwich
-- statement:
--   All Hilbert spaces are finite dimensional and complex; all logarithms are binary. Positive-operator inequalities use the identity when comparing with a scalar. Let $\rho$ be normalized, $\sigma\ge0$, $\varepsilon\ge0$, $\delta>0$, and $\varepsilon+\delta\le1$. Define $D_s^a(\rho\Vert\sigma)=\sup\{R:\operatorname{tr}\rho\{\rho\le2^R\sigma\}\le a\}$, using the weak spectral projector and extended-real supremum. Then
--   $$D_s^\varepsilon(\rho\Vert\sigma)\le D_h^\varepsilon(\rho\Vert\sigma)\le D_s^{\varepsilon+\delta}(\rho\Vert\sigma)-\log\delta.$$
--   No support-inclusion assumption is imposed; infinite divergences are retained.
-- source:
--   A Hierarchy of Information Quantities for Finite Block Length Analysis of Quantum Tasks, arXiv:1208.1478v3, PDF p. 14, Lemma 12: spectrum/testing sandwich

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

/-- Lemma 12, PDF p.14: no support inclusion; infinite values retained. -/
theorem spectrum_testing_sandwich (rho sigma : Mat I) (hrho : QAlgorithms.IsDensityMatrix rho)
    (hsigma : sigma.PosSemidef) (e delta : ℝ) (he : 0 ≤ e) (hdelta : 0 < delta)
    (hdomain : e + delta ≤ 1) :
    spectrumEntropy e rho sigma ≤ extendedTestingDivergence e rho sigma ∧
    extendedTestingDivergence e rho sigma ≤ spectrumEntropy (e+delta) rho sigma - (logTwo delta : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P02

end
