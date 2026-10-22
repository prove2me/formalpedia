-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P41_strong_converse_exponent_bound
-- name    : QAlgorithms.Papers.Independent.Gap48.P41.strong_converse_exponent_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:30:09.27238+00:00
-- url     : https://prove2.me/theorems/3ae837d7-6f32-451f-9015-d4de9a97036a
-- title:
--   Strong-converse exponent bound and constructed crossing
-- statement:
--   Let $I$ be a nonempty finite orthonormal basis, and let $\rho,\sigma$ be positive semidefinite complex matrices of trace one with $\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma$. For a positive integer $n$, an arbitrary effect $0\le A_n\le I$ accepts the null state $\rho^{\otimes n}$. Write $\alpha_n(A_n)=\operatorname{Tr}[\rho^{\otimes n}(I-A_n)]$ and $\beta_n(A_n)=\operatorname{Tr}[\sigma^{\otimes n}A_n]$. All logarithms are natural, with $\log0=-\infty$ in rates. Write $D(\rho\Vert\sigma)=\operatorname{Tr}[\rho(\log\rho-\log\sigma)]$, using support-restricted spectral logarithms inside the trace.
--
--   Put $\psi(s)=\log\operatorname{Tr}(\rho^{1+s}\sigma^{-s})$ and $\phi(\lambda)=\max_{0\le s\le1}\{\lambda s-\psi(s)\}$. Spectral powers vanish on the kernel, including at zero and negative orders.
--
--   For any real $r$, define
--   $$
--   u(r)=\max_{0\le s\le1}\frac{s r-\psi(s)}{1+s},\qquad \lambda_*(r)=r-u(r).
--   $$
--   The maximum is attained and $\phi(\lambda_*)=r-\lambda_*=u(r)$. For every sequence of effects,
--   $$
--   \limsup_{n\to\infty}\frac1n\log\beta_n(A_n)\le-r
--   \quad\Longrightarrow\quad
--   \limsup_{n\to\infty}\frac1n\log(1-\alpha_n(A_n))\le-\phi(\lambda_*).
--   $$
--   If $D(\rho\Vert\sigma)\le r\le2\psi'(1)-\psi(1)$, some $s_*\in[0,1]$ satisfies
--   $$
--   u(r)=s_*\psi'(s_*)-\psi(s_*),\qquad r=(1+s_*)\psi'(s_*)-\psi(s_*).
--   $$
--   This is a bound for every real rate, including the endpoint branches; it asserts no optimality of the quantum exponent.
-- source:
--   Strong Converse and Stein's Lemma in the Quantum Hypothesis Testing, arXiv:quant-ph/9906090v1, PDF p. 5, §4, Theorem 3, (13)–(17): strong-converse exponent bound

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

/-- PDF pp.5--6, Theorem 3, (13)--(17): limsup bound for every real r, the
constructed crossing, attained compact maximum, and interior parametrization.
This is the paper's Petz bound, not the later optimal sandwiched exponent. -/
theorem strong_converse_exponent_bound [Nonempty I]
    (rho sigma : Mat I) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hsupp : SupportLE rho sigma) (r : ℝ) (A : TestSequence I)
    (hrate : limsup (fun k => scaled k (logNonnegativeExtended
      (accept sigma (k + 1) (A k).1))) atTop ≤ -(r : EReal)) :
    petzPhi rho sigma (crossing rho sigma r) = r - crossing rho sigma r ∧
    petzPhi rho sigma (crossing rho sigma r) = petzExponent rho sigma r ∧
    IsGreatest (petzG rho sigma r '' Set.Icc 0 1) (petzExponent rho sigma r) ∧
    limsup (fun k => scaled k (logNonnegativeExtended
      (1 - typeI rho (k + 1) (A k).1))) atTop ≤
        -((petzPhi rho sigma (crossing rho sigma r)) : EReal) ∧
    ((relativeEntropy rho sigma).toReal ≤ r ∧
      r ≤ 2 * deriv (petzPsi rho sigma) 1 - petzPsi rho sigma 1 →
      ∃ s ∈ Set.Icc (0 : ℝ) 1,
        petzExponent rho sigma r = s * deriv (petzPsi rho sigma) s - petzPsi rho sigma s ∧
        r = (1 + s) * deriv (petzPsi rho sigma) s - petzPsi rho sigma s) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P41

end
