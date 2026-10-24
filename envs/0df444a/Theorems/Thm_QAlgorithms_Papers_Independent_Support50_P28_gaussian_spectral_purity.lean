-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P28_gaussian_spectral_purity
-- name    : QAlgorithms.Papers.Independent.Support50.P28.gaussian_spectral_purity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:12:58.430748+00:00
-- url     : https://prove2.me/theorems/e406c6eb-4304-45d4-8240-057c54197a93
-- title:
--   Section III, (27)–(29): Gaussian spectral p-purity formula
-- statement:
--   Let $n\ge1$ and let $\rho$ be an actual normalized centered Gaussian density with real symmetric physical doubled covariance $\gamma$. Let $\nu_1,\ldots,\nu_n\ge1$ be its symplectic eigenvalues, counted once per mode, identified by a Williamson congruence. For real $p>1$, define $f_p(x)=(x+1)^p-(x-1)^p$ and $F_p(\gamma)=\prod_{j=1}^n f_p(\nu_j)$. Then
--
--   $$\operatorname{Tr}\rho^p=\prod_{j=1}^n\frac{2^p}{f_p(\nu_j)}=\frac{2^{pn}}{F_p(\gamma)},\qquad \mu(\rho):=\operatorname{Tr}\rho^2=\frac1{\prod_j\nu_j}=\frac1{\sqrt{\det\gamma}}.$$
--
--   This computes spectral trace powers from covariance data. The ordinary purity is the square of the Schatten $2$-norm. The trace power is independently defined by the actual density's spectral functional calculus. The bounded operator used in that calculus is required, in the theorem's conclusion, to realize the original density coefficients.
-- source:
--   Multiplicativity of maximal output purities of Gaussian channels under Gaussian inputs, arXiv:quant-ph/0406065v1, PDF p. 4, Section III, (27)–(29): Gaussian spectral p-purity formula

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P28

noncomputable section

open scoped BigOperators ENNReal ComplexOrder Matrix

namespace QAlgorithms.Papers.Independent.Support50.P28

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClassChannel rankOne)

open QAlgorithms.Papers.Independent.Claimed50.P47
  (Occupation gaussianStateCharacteristic singleCharacteristic weylKernel)

open QAlgorithms.Papers.Independent.Claimed50.P30 (phiMinus)

/-- PDF p.4, (27)--(29): spectral trace power and ordinary purity of a centered
Gaussian density. Physical normalization follows the proof, correcting (6),(7).
A Williamson spectrum identifies the symplectic eigenvalues without assuming a
normal-state decomposition or any trace-power formula. -/
theorem gaussian_spectral_purity {n : ℕ} (hn : 0 < n)
    (rho : State (Occupation (Fin n))) (G : OscillatorCovariance (Fin n))
    (hG : HasCenteredGaussianCovariance rho G) (nu : Fin n → ℝ)
    (hnu : WilliamsonSpectrum G nu) (p : ℝ) (hp : 1 < p) :
    oscillatorCoefficients (realizeOscillatorCoeff rho.coefficients) = rho.coefficients ∧
    tracePower p rho.coefficients =
      ENNReal.ofReal (∏ i, Real.rpow 2 p / fp p (nu i)) ∧
    tracePower p rho.coefficients =
      ENNReal.ofReal (Real.rpow 2 (p * n) / spectralFp p nu) ∧
    tracePower 2 rho.coefficients = ENNReal.ofReal (1 / ∏ i, nu i) ∧
    tracePower 2 rho.coefficients = ENNReal.ofReal (1 / Real.sqrt G.det) := by sorry

end QAlgorithms.Papers.Independent.Support50.P28

end
