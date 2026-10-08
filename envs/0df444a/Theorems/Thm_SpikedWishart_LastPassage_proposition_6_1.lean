-- Prove2me | Theorems.Thm_SpikedWishart_LastPassage_proposition_6_1
-- name    : SpikedWishart.LastPassage.proposition_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:37:05.655537+00:00
-- url     : https://prove2.me/theorems/b8c3944b-b6a9-4eb5-9667-0296e690c9bc
-- title:
--   Proposition 6.1, p. 1692 — the exponential last passage time L(N, M) and the largest sample eigenvalue λ₁ have the same law
-- statement:
--   Let $1 \le N \le M$ and let $\pi_1,\ldots,\pi_N$ be positive numbers. Let $X(i,j)$, $1\le i\le N$, $1\le j\le M$, be independent exponential random variables, $X(i,j)$ of mean $1/(\pi_iM)$, and let $L(N,M)$ be the last passage time from $(1,1)$ to $(N,M)$ (306).
--
--   Let $U$ be any $N\times N$ unitary matrix, set $\ell_j = \pi_j^{-1}$ (308), and let $\vec y_1,\ldots,\vec y_M$ be independent mean-zero complex Gaussian vectors in $\mathbb C^N$ with covariance $\Sigma = U\,\mathrm{diag}(\ell_1,\ldots,\ell_N)\,U^*$. Let $\lambda_1(M,N)$ be the largest eigenvalue of the sample covariance matrix $S = \frac1M\sum_{k=1}^M \vec y_k\vec y_k^{\,*}$. Then for every $x\in\mathbb R$,
--   $$\mathbb P\big(L(N,M) \le x\big) = \mathbb P\big(\lambda_1(M,N) \le x\big).$$
--
--   The identity transfers every result about $\lambda_1$ in the paper, in particular the phase transition of Theorem 1.1, to last passage percolation with row-dependent exponential rates and to the equivalent tandem queue.
--
--   **Formalization Note** The proposition writes $L(M,N)$; (306)–(307) define the object as $L(N,M)$ with $N$ rows of rate $\pi_iM$ and $M$ columns, and that object is used. The hypothesis $N \le M$ is added: the proposition is derived from (307), which the page states for $M \ge N$, and "as in the Introduction" has $M \ge N$. The sample model is mean zero without centring and with normalisation $1/M$ (see the definition file); the identity is exact only for this model. The population covariance is $U\,\mathrm{diag}(\pi^{-1})\,U^*$ for every unitary $U$, and the $\pi_i$ need not be distinct.
-- source:
--   Baik, Ben Arous and Péché, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), p. 1692, Proposition 6.1, (308)–(309)

import Mathlib
import Definitions.Def_SpikedWishart_LastPassage_Model
import Definitions.Def_SpikedWishart_LastPassage_LPP

namespace SpikedWishart.LastPassage

open MeasureTheory ProbabilityTheory

/-- Proposition 6.1: the last passage time `L(N, M)` with independent exponential site variables
of rate `π_i M` has the same distribution as the largest eigenvalue `λ₁` of the sample covariance
matrix of `M` complex Gaussian samples of `N × 1` vectors with population covariance
`Σ = U diag(π⁻¹) U*`, i.e. `ℓ_i = π_i⁻¹` (308). -/
theorem proposition_6_1 {N M : ℕ} [NeZero N] [NeZero M] (hNM : N ≤ M) (π : Fin N → ℝ)
    (hπ : ∀ i, 0 < π i) (U : Matrix.unitaryGroup (Fin N) ℂ) (x : ℝ) :
    (expLaw π M).real {X | L X ≤ x} =
      (sampleLaw M N).real {G | SpikedWishart.SoftEdge.largestEig M U (fun i => (π i)⁻¹) G ≤ x} := by sorry

end SpikedWishart.LastPassage
