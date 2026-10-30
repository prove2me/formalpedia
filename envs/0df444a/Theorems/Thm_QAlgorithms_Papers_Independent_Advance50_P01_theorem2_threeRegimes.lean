-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P01_theorem2_threeRegimes
-- name    : QAlgorithms.Papers.Independent.Advance50.P01.theorem2_threeRegimes
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:58:57.424239+00:00
-- url     : https://prove2.me/theorems/91d982d3-b98f-4aa8-981b-ae41e6202479
-- title:
--   Theorem 2: three regimes of the optimal type-I error
-- statement:
--   Let $\rho$ and $\sigma$ be positive semidefinite complex matrices of trace one on a common nonzero finite-dimensional Hilbert space, with $\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma$. All logarithms are natural. Write $D=\operatorname{Tr}[\rho(\log\rho-\log\sigma)]$ and $V=\operatorname{Tr}[\rho(\log\rho-\log\sigma)^2]-D^2$, with zero kernel contributions. Tests are all binary POVMs $(A,I-A)$ on the $n$-fold tensor product; their conditional errors are $\alpha_n(A)=\operatorname{Tr}[\rho^{\otimes n}(I-A)]$ and $\beta_n(A)=\operatorname{Tr}[\sigma^{\otimes n}A]$. Let $\Phi$ denote the standard normal cumulative distribution function.
--
--   For fixed real $E_1,E_2$ and fixed $f:\mathbb N\to\mathbb R$, define $a_n$ as the minimum of $\alpha_n(A)$ subject to $\beta_n(A)\le e^{-nE_1-\sqrt n E_2-f(n)}$. Then
--
--   $$\lim_{n\to\infty}a_n=\begin{cases}0,&E_1<D,\ f=o(n),\\\Phi(E_2/\sqrt V),&E_1=D,\ V>0,\ f=o(\sqrt n),\\1,&E_1>D,\ f=o(n).\end{cases}$$
--
--   The result resolves the transition at the relative-entropy threshold. The first and third branches also cover zero variance.
-- source:
--   Second-order asymptotics for quantum hypothesis testing, arXiv:1208.1400v3, PDF p. 5, Theorem 2

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

/-- Theorem 2, source PDF pp. 5–6. All three regimes are retained. The central branch
has V>0, the nonsingular domain identified on p. 17; the other branches allow V=0. -/
theorem theorem2_threeRegimes [Nonempty I] (rho sigma : Matrix I I ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hsupport : SupportIncluded rho sigma) (E1 E2 : ℝ) (f : ℕ → ℝ) :
    ((E1 < relativeEntropyNats rho sigma ∧
        (f =o[atTop] (fun n : ℕ => (n : ℝ)))) →
      Tendsto (constrainedTypeI rho sigma E1 E2 f) atTop (nhds 0)) ∧
    ((E1 = relativeEntropyNats rho sigma ∧ 0 < relativeVarianceNats rho sigma ∧
        (f =o[atTop] (fun n : ℕ => Real.sqrt (n : ℝ)))) →
      Tendsto (constrainedTypeI rho sigma E1 E2 f) atTop
        (nhds (normalCDF (E2 / Real.sqrt (relativeVarianceNats rho sigma))))) ∧
    ((relativeEntropyNats rho sigma < E1 ∧
        (f =o[atTop] (fun n : ℕ => (n : ℝ)))) →
      Tendsto (constrainedTypeI rho sigma E1 E2 f) atTop (nhds 1)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P01

end
