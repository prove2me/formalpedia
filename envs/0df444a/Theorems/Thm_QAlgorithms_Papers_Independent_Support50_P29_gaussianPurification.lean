-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P29_gaussianPurification
-- name    : QAlgorithms.Papers.Independent.Support50.P29.gaussianPurification
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:15:31.47599+00:00
-- url     : https://prove2.me/theorems/11c55a68-6b4e-418f-a22d-8fd541dcf114
-- title:
--   Reflected Gaussian purification
-- statement:
--   Let $s\ge1$, $\hbar>0$, and $\Delta=\hbar\begin{bmatrix}0&I\\-I&0\end{bmatrix}$. Let $\rho$ be a normalized centered Gaussian state of a regular irreducible canonical Weyl system on a nonzero complete separable Hilbert space, with real symmetric covariance $\alpha$ satisfying $\alpha-i\Delta/2\ge0$. Choose a second regular irreducible oscillator system and reflect its reference coordinates by exchanging $q$ and $p$, so its CCR form is $-\Delta$. Set
--   $$
--   S=\sqrt{-(\Delta^{-1}\alpha)^2-I/4},\qquad
--   \alpha_{12}=\begin{bmatrix}\alpha&\Delta S\\-\Delta S&\alpha\end{bmatrix},\qquad
--   \Delta_{12}=\operatorname{diag}(\Delta,-\Delta).
--   $$
--   The square root is the nonnegative branch of similarity spectral calculus. There exists a normalized Gaussian density $\rho_{12}$ on the completed tensor product, with characteristic $\exp(-z^T\alpha_{12}z/2)$, such that
--   $$
--   \operatorname{Tr}_2\rho_{12}=\rho,\qquad \rho_{12}=|\psi\rangle\langle\psi|\quad(\|\psi\|=1),\qquad
--   (\Delta_{12}^{-1}\alpha_{12})^2=-I/4.
--   $$
--   Thus the displayed covariance specifies an actual pure state and the correct marginal, not merely a physical covariance witness. The paper acknowledges the construction's provenance in Holevo [4].
-- source:
--   Sending Quantum Information with Gaussian States, arXiv:quant-ph/9809022v1, PDF p. 6, §3, unnumbered: constructed Gaussian purification with reflected CCR

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P29

noncomputable section

open Filter

open scoped BigOperators ENNReal Topology ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Support50.P29

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma complexify)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity rankOne productCoeff tensorApply IsTraceClassChannel)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedEntropyNats)

open QAlgorithms.Papers.Independent.Frontier30.P10 (WeylSystem)

open QAlgorithms.Papers.Independent.Frontier30.P14 (partialRight PureDensity)

open QAlgorithms.Papers.Independent.Claimed50.P35
  (tracePair thermalInput thermalPurificationDensity vacuumChannel exchangeMatrix RealizedDensity)

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

open QAlgorithms.Papers.Independent.Information100.P49 (thermalEntropy)

/-- Holevo quant-ph/9809022v1, PDF pp.6-7, §3: reflected-reference
Gaussian purification with the displayed covariance, actual partial trace,
and norm-one rank-one purity. The source acknowledges construction [4]. -/
theorem gaussianPurification {I J : Type} [Countable I] [Countable J]
    [Nonempty I] [Nonempty J] (s : ℕ) (hs : 0 < s)
    (hbar : ℝ) (hhbar : 0 < hbar)
    (W : WeylSystem (Hilbert I) s) (V : WeylSystem (Hilbert J) s)
    (rho : State I) (alpha : Matrix (Phase s) (Phase s) ℝ)
    (hrho : CenteredGaussianWithCovariance hbar W rho alpha) :
    (∃ rho12 : State (I × J),
      PureDensity rho12.coefficients ∧
      partialRight rho12.coefficients = rho.coefficients ∧
      (∀ z, jointCharacteristic hbar W V rho12.coefficients z =
        centeredCharacteristic (purificationCovariance hbar alpha) z)) ∧
    (((reflectedDelta s hbar)⁻¹ * purificationCovariance hbar alpha) ^ 2 =
      (-1 / 4 : ℝ) • 1) := by sorry

end QAlgorithms.Papers.Independent.Support50.P29

end
