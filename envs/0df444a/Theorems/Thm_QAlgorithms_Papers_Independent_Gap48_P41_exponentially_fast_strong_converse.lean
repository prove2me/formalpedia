-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P41_exponentially_fast_strong_converse
-- name    : QAlgorithms.Papers.Independent.Gap48.P41.exponentially_fast_strong_converse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:30:58.063001+00:00
-- url     : https://prove2.me/theorems/9a06e431-c77a-426a-a154-0e46b0353e2a
-- title:
--   Strict type-II rate gap forces exponentially vanishing success
-- statement:
--   Let $I$ be a nonempty finite orthonormal basis, and let $\rho,\sigma$ be positive semidefinite complex matrices of trace one with $\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma$. For a positive integer $n$, an arbitrary effect $0\le A_n\le I$ accepts the null state $\rho^{\otimes n}$. Write $\alpha_n(A_n)=\operatorname{Tr}[\rho^{\otimes n}(I-A_n)]$ and $\beta_n(A_n)=\operatorname{Tr}[\sigma^{\otimes n}A_n]$. All logarithms are natural, with $\log0=-\infty$ in rates. Write $D(\rho\Vert\sigma)=\operatorname{Tr}[\rho(\log\rho-\log\sigma)]$, using support-restricted spectral logarithms inside the trace.
--
--   For every sequence of effects with
--   $$
--   \limsup_{n\to\infty}\frac1n\log\beta_n(A_n)<-D(\rho\Vert\sigma),
--   $$
--   there are $c>0$ and a positive threshold $N$ such that
--   $$
--   1-\alpha_n(A_n)\le e^{-c n}\qquad(n\ge N).
--   $$
--   In particular, $\alpha_n(A_n)\to1$. This gives the paper's exponential strong converse, with the decay rate concluded from the strict gap.
-- source:
--   Strong Converse and Stein's Lemma in the Quantum Hypothesis Testing, arXiv:quant-ph/9906090v1, PDF p. 7, §4, Corollary 1, (18): exponentially fast strong converse

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P41

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P41

open scoped Matrix ComplexOrder BigOperators

open Filter QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Information100.P07 (positiveProjection)

open QAlgorithms.Papers.Independent.Dependency50.P28
  (tr SupportLE relativeEntropy scalarPower classicalD typeI accept TestSequence
    scaled logNonnegativeExtended)

open QAlgorithms.Papers.Independent.Claimed50.P15 (legendre)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I : Type} [Fintype I] [DecidableEq I]

/-- PDF p.7, Corollary 1, (18): a strict type-II rate gap forces exponential
convergence of alpha to one. Constants are chosen before the block index. -/
theorem exponentially_fast_strong_converse [Nonempty I]
    (rho sigma : Mat I) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hsupp : SupportLE rho sigma) (A : TestSequence I)
    (hrate : limsup (fun k => scaled k (logNonnegativeExtended
      (accept sigma (k + 1) (A k).1))) atTop < -relativeEntropy rho sigma) :
    (∃ c : ℝ, 0 < c ∧ ∃ K : ℕ, ∀ k ≥ K,
      1 - typeI rho (k + 1) (A k).1 ≤ Real.exp (-c * ((k + 1 : ℕ) : ℝ))) ∧
    Tendsto (fun k => typeI rho (k + 1) (A k).1) atTop (nhds 1) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P41

end
