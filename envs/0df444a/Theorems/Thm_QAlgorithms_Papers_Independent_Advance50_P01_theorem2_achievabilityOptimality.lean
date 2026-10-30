-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P01_theorem2_achievabilityOptimality
-- name    : QAlgorithms.Papers.Independent.Advance50.P01.theorem2_achievabilityOptimality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:00:20.115248+00:00
-- url     : https://prove2.me/theorems/932a6810-1dbf-4e26-9cb0-50e543acf006
-- title:
--   Reformulation of Theorem 2: achievability and optimality
-- statement:
--   Let $\rho$ and $\sigma$ be positive semidefinite complex matrices of trace one on a common nonzero finite-dimensional Hilbert space, with $\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma$. All logarithms are natural. Write $D=\operatorname{Tr}[\rho(\log\rho-\log\sigma)]$ and $V=\operatorname{Tr}[\rho(\log\rho-\log\sigma)^2]-D^2$, with zero kernel contributions. Tests are all binary POVMs $(A,I-A)$ on the $n$-fold tensor product; their conditional errors are $\alpha_n(A)=\operatorname{Tr}[\rho^{\otimes n}(I-A)]$ and $\beta_n(A)=\operatorname{Tr}[\sigma^{\otimes n}A]$. Let $\Phi$ denote the standard normal cumulative distribution function.
--
--   Assume $V>0$, fix $E_2\in\mathbb R$ and $f=o(\sqrt n)$, and put $b_n=\exp[-nD-E_2\sqrt n-f(n)]$. There exists a sequence of binary POVMs with $\beta_n(A_n)\le b_n$ for every positive integer $n$ and
--
--   $$\limsup_{n\to\infty}\alpha_n(A_n)\le\Phi(E_2/\sqrt V).$$
--
--   Conversely, every sequence satisfying these same type-II bounds obeys
--
--   $$\liminf_{n\to\infty}\alpha_n(A_n)\ge\Phi(E_2/\sqrt V).$$
--
--   This separates attainability from the converse while preserving optimization over all POVMs.
-- source:
--   Second-order asymptotics for quantum hypothesis testing, arXiv:1208.1400v3, PDF p. 6, Reformulation of Theorem 2

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

/-- Reformulation of Theorem 2, source PDF p. 6, (4)–(7), with V>0 (p. 17).
Achievability chooses a sequence of arbitrary binary POVMs; optimality covers every such sequence. -/
theorem theorem2_achievabilityOptimality [Nonempty I] (rho sigma : Matrix I I ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hsupport : SupportIncluded rho sigma) (hV : 0 < relativeVarianceNats rho sigma)
    (E2 : ℝ) (f : ℕ → ℝ) (hf : f =o[atTop] (fun n : ℕ => Real.sqrt (n : ℝ))) :
    (∃ A : (n : ℕ) → IIDTest I n,
      (∀ n, 1 ≤ n → typeII sigma (A n) ≤
        Real.exp (-(n * relativeEntropyNats rho sigma + E2 * Real.sqrt n + f n))) ∧
      Filter.limsup (fun n => iidTypeI rho (A n)) atTop ≤
        normalCDF (E2 / Real.sqrt (relativeVarianceNats rho sigma))) ∧
    (∀ A : (n : ℕ) → IIDTest I n,
      (∀ n, 1 ≤ n → typeII sigma (A n) ≤
        Real.exp (-(n * relativeEntropyNats rho sigma + E2 * Real.sqrt n + f n))) →
      normalCDF (E2 / Real.sqrt (relativeVarianceNats rho sigma)) ≤
        Filter.liminf (fun n => iidTypeI rho (A n)) atTop) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P01

end
