-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P41_fundamental_error_bound
-- name    : QAlgorithms.Papers.Independent.Gap48.P41.fundamental_error_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:28:44.231592+00:00
-- url     : https://prove2.me/theorems/c2321e18-6f91-40a7-bff2-93cc5ffa3b7d
-- title:
--   Fundamental finite-block error inequality
-- statement:
--   Let $I$ be a nonempty finite orthonormal basis, and let $\rho,\sigma$ be positive semidefinite complex matrices of trace one with $\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma$. For a positive integer $n$, an arbitrary effect $0\le A_n\le I$ accepts the null state $\rho^{\otimes n}$. Write $\alpha_n(A_n)=\operatorname{Tr}[\rho^{\otimes n}(I-A_n)]$ and $\beta_n(A_n)=\operatorname{Tr}[\sigma^{\otimes n}A_n]$. All logarithms are natural, with $\log0=-\infty$ in rates. Write $D(\rho\Vert\sigma)=\operatorname{Tr}[\rho(\log\rho-\log\sigma)]$, using support-restricted spectral logarithms inside the trace.
--
--   Put $\psi(s)=\log\operatorname{Tr}(\rho^{1+s}\sigma^{-s})$ and $\phi(\lambda)=\max_{0\le s\le1}\{\lambda s-\psi(s)\}$. Spectral powers vanish on the kernel, including at zero and negative orders.
--
--   The maximum defining $\phi$ is attained. For every positive $n$, every $\lambda\in\mathbb R$, and every effect $A_n$,
--   $$
--   1-\alpha_n(A_n)\le e^{-n\phi(\lambda)}+e^{n\lambda}\beta_n(A_n).
--   $$
--   This finite-block inequality provides the quantitative link between the two testing errors.
-- source:
--   Strong Converse and Stein's Lemma in the Quantum Hypothesis Testing, arXiv:quant-ph/9906090v1, PDF p. 3, §2, Theorem 1, (6)–(8): fundamental finite-block error bound

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

/-- PDF pp.3--4, Theorem 1, (6)--(8): the finite-block fundamental bound.
The maximum defining phi is attained on [0,1], not on all nonnegative orders. -/
theorem fundamental_error_bound [Nonempty I]
    (rho sigma : Mat I) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hsupp : SupportLE rho sigma) (n : ℕ) (hn : 0 < n) (lambda : ℝ)
    (A : Mat (Fin n → I)) (hA : IsEffect A) :
    IsGreatest ((fun s : ℝ => lambda * s - petzPsi rho sigma s) '' Set.Icc 0 1)
      (petzPhi rho sigma lambda) ∧
    1 - typeI rho n A ≤ Real.exp (-(n : ℝ) * petzPhi rho sigma lambda) +
      Real.exp ((n : ℝ) * lambda) * accept sigma n A := by sorry

end QAlgorithms.Papers.Independent.Gap48.P41

end
