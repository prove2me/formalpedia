-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P29_exchangeCovarianceAndSpectrum
-- name    : QAlgorithms.Papers.Independent.Support50.P29.exchangeCovarianceAndSpectrum
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:16:37.227994+00:00
-- url     : https://prove2.me/theorems/634bb04c-d1db-4093-ad81-9f24ab4d0aa4
-- title:
--   Extended output covariance and corrected spectrum
-- statement:
--   Let $N\ge0$, $k\ge0$, and $\hbar>0$. Let $\widetilde\rho_{12}=(T_k\otimes\mathrm{Id})(\rho_{12})$ be the actual channel output on the normalized thermal Schmidt purification, with the reference quadratures reflected. Write $\widetilde N=k^2N$ for $k\le1$ and $\widetilde N=k^2N+k^2-1$ for $k>1$, and put $B=k\sqrt{N(N+1)}\,\Delta$, where $\Delta=\hbar\begin{bmatrix}0&1\\-1&0\end{bmatrix}$. The output is a normalized Gaussian density with covariance
--   $$
--   \widetilde\alpha_{12}=\begin{bmatrix}\hbar(\widetilde N+1/2)I&B\\-B&\hbar(N+1/2)I\end{bmatrix}.
--   $$
--   Under the explicit realification and subsystem permutation, $\Delta_{12}^{-1}\widetilde\alpha_{12}$ corresponds to
--   $$
--   M=\begin{bmatrix}i(\widetilde N+1/2)&k\sqrt{N(N+1)}\\k\sqrt{N(N+1)}&-i(N+1/2)\end{bmatrix}.
--   $$
--   Its two eigenvalues, with multiplicity, are $i/2$ and $-i((1-k^2)N+1/2)$ for $k<1$; for $k>1$ they are $-i/2$ and $i((k^2-1)(N+1)+1/2)$. The actual output characteristic equals $\exp(-z^T\widetilde\alpha_{12}z/2)$. This identifies the state covariance as well as the matrix spectrum used in entropy exchange.
-- source:
--   Sending Quantum Information with Gaussian States, arXiv:quant-ph/9809022v1, PDF p. 9, §4, unnumbered: extended output covariance and exchange spectrum

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

/-- Holevo quant-ph/9809022v1, PDF p.9, §4: actual reflected extended
output covariance and both eigenvalues with multiplicities. SOURCE CORRECTION:
the printed common lambda1=i/2 becomes -i/2 for k>1; at N=0,k=sqrt(2)
the matrix is diag(3i/2,-i/2), so the printed sign has the wrong trace. -/
theorem exchangeCovarianceAndSpectrum (N k hbar : ℝ)
    (hN : 0 ≤ N) (hk : 0 ≤ k) (hhbar : 0 < hbar) :
    RealizedDensity (exchangeOutput N k) ∧
    (∀ z, jointFockCharacteristic hbar (exchangeOutput N k) z =
      centeredCharacteristic (exchangeCovariance hbar N k) z) ∧
    (reflectedDelta 1 hbar)⁻¹ * exchangeCovariance hbar N k =
      oneModeRealification (exchangeMatrix N k 0) ∧
    (k < 1 → (exchangeMatrix N k 0).charpoly =
      (Polynomial.X - Polynomial.C (Complex.I / 2)) *
      (Polynomial.X - Polynomial.C
        (-Complex.I * (((1 - k ^ 2) * N + 1 / 2 : ℝ) : ℂ)))) ∧
    (1 < k → (exchangeMatrix N k 0).charpoly =
      (Polynomial.X - Polynomial.C (-Complex.I / 2)) *
      (Polynomial.X - Polynomial.C
        (Complex.I * (((k ^ 2 - 1) * (N + 1) + 1 / 2 : ℝ) : ℂ)))) := by sorry

end QAlgorithms.Papers.Independent.Support50.P29

end
