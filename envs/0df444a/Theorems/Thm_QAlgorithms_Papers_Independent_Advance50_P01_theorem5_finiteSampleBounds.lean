-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P01_theorem5_finiteSampleBounds
-- name    : QAlgorithms.Papers.Independent.Advance50.P01.theorem5_finiteSampleBounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:03:56.255649+00:00
-- url     : https://prove2.me/theorems/b9e45eee-f9b4-49a4-a515-10ae17ac020b
-- title:
--   Theorem 5: explicit finite-sample upper and lower testing bounds
-- statement:
--   Let $\rho$ and $\sigma$ be positive semidefinite complex matrices of trace one on a common nonzero finite-dimensional Hilbert space, with $\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma$. All logarithms are natural. Write $D=\operatorname{Tr}[\rho(\log\rho-\log\sigma)]$ and $V=\operatorname{Tr}[\rho(\log\rho-\log\sigma)^2]-D^2$, with zero kernel contributions. Tests are all binary POVMs $(A,I-A)$ on the $n$-fold tensor product; their conditional errors are $\alpha_n(A)=\operatorname{Tr}[\rho^{\otimes n}(I-A)]$ and $\beta_n(A)=\operatorname{Tr}[\sigma^{\otimes n}A]$. Let $\Phi$ denote the standard normal cumulative distribution function.
--
--   Assume $V>0$ and fix $0<\varepsilon<1$. Let $C$ be a valid universal Berry–Esseen constant, independent of the states, bases, sample size and tolerance, with $0.40973\le C\le0.4784$. For any complete spectral presentations let $P(x,y)=\lambda_x|\langle b_y|a_x\rangle|^2$ and $T^3=\mathbb E_P|\log(\lambda_X/\mu_Y)-D|^3$. Zero-weight terms are zero. Define $\beta_n^*(\varepsilon)=\min_{\alpha_n(A)\le\varepsilon}\beta_n(A)$, $H_n=-\log\beta_n^*(\varepsilon)$ and $\delta_n=CT^3/[\sqrt n(\sqrt V)^3]$. For every integer $n\ge1$, the following bounds hold whenever their respective shifted-tolerance conditions hold:
--
--   $$\begin{aligned}\varepsilon-\delta_n\ge0&\ \Longrightarrow\ H_n\ge L_n:=nD+\sqrt n\sqrt V\,\Phi^{-1}(\varepsilon-\delta_n),\\\varepsilon+\delta_n+2/\sqrt n\le1&\ \Longrightarrow\ H_n\le U_n:=nD+\sqrt n\sqrt V\,\Phi^{-1}(\varepsilon+\delta_n+2/\sqrt n)+\log(2^9n^2).\end{aligned}$$
--
--   Use $\Phi^{-1}(0)=-\infty$ and $\Phi^{-1}(1)=+\infty$. For sufficiently large $n$, both arguments are interior and, with $c_n=nD+\sqrt n\sqrt V\,\Phi^{-1}(\varepsilon)$,
--
--   $$L_n=c_n+O(1),\qquad U_n=c_n+2\log n+O(1).$$
--
--   These are separate finite bounds and expansions of the bounding expressions. In particular the theorem does not identify the optimized remainder with either bounding remainder.
-- source:
--   Second-order asymptotics for quantum hypothesis testing, arXiv:1208.1400v3, PDF p. 15, Theorem 5, equations (44)–(45)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P01

noncomputable section

open Filter

open scoped Topology

namespace QAlgorithms.Papers.Independent.Advance50.P01

open QAlgorithms.Papers.Independent.Information100.P71 (SupportIncluded)

open QAlgorithms.Papers.Independent.Information100.P63 (normalCDF normalQuantile tensorPower)

open QAlgorithms.Papers.Independent.Information100.P58 (testingBeta testingD)

open QAlgorithms.Papers.Independent.Dependency50.P36 (relativeEntropyFinite)

attribute [local instance] Classical.propDecidable

-- Match the universe-zero matrix indices of the pinned accepted interfaces.

variable {I : Type} [Fintype I] [DecidableEq I]

-- SupportIncluded is opened directly from the accepted Information100.P71 module.

/-- Theorem 5, source PDF pp. 14–16, (44)–(45). Each finite inequality has its own
weak shifted-epsilon condition and n>=1. Extended quantiles retain the endpoints.
The final clauses expand the bounding expressions, not the optimized divergence itself.
Zero-weight sigma-kernel terms implement compression (p. 5). -/
theorem theorem5_finiteSampleBounds (C : ℝ) (hC : IsBerryEsseenConstant C)
    (hCrange : (0.40973 : ℝ) ≤ C ∧ C ≤ (0.4784 : ℝ))
    [Nonempty I] (rho sigma : Matrix I I ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hsupport : SupportIncluded rho sigma) (hV : 0 < relativeVarianceNats rho sigma)
    (r : SpectralDecomposition rho) (s : SpectralDecomposition sigma)
    (epsilon : ℝ) (hepsilon : 0 < epsilon ∧ epsilon < 1) :
    (∀ n : ℕ, 1 ≤ n →
      0 ≤ epsilon - beCorrection C (relativeVarianceNats rho sigma) (spectralThirdMoment r s) n →
      finiteLower rho sigma epsilon C (spectralThirdMoment r s) n ≤
        iidTestingDivergenceNats rho sigma n epsilon) ∧
    (∀ n : ℕ, 1 ≤ n →
      epsilon + beCorrection C (relativeVarianceNats rho sigma) (spectralThirdMoment r s) n +
          2 / Real.sqrt n ≤ 1 →
      iidTestingDivergenceNats rho sigma n epsilon ≤
        finiteUpper rho sigma epsilon C (spectralThirdMoment r s) n) ∧
    (∃ lowerRemainder upperRemainder : ℕ → ℝ,
      (lowerRemainder =O[atTop] (fun _ : ℕ => (1 : ℝ))) ∧
      (upperRemainder =O[atTop] (fun _ : ℕ => (1 : ℝ))) ∧
      ∃ N : ℕ, 1 ≤ N ∧ ∀ n ≥ N,
        0 < epsilon - beCorrection C (relativeVarianceNats rho sigma) (spectralThirdMoment r s) n ∧
        epsilon + beCorrection C (relativeVarianceNats rho sigma) (spectralThirdMoment r s) n +
            2 / Real.sqrt n < 1 ∧
        finiteLower rho sigma epsilon C (spectralThirdMoment r s) n =
          ((secondOrderCenter rho sigma epsilon n + lowerRemainder n : ℝ) : EReal) ∧
        finiteUpper rho sigma epsilon C (spectralThirdMoment r s) n =
          ((secondOrderCenter rho sigma epsilon n + 2 * Real.log n +
            upperRemainder n : ℝ) : EReal)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P01

end
