-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_analytic_finite
-- name    : TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_finite
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-24T13:21:57.743893+00:00
-- url     : https://prove2.me/theorems/7c1e7cb4-907c-4ef7-8622-bc5873ed4f44
-- title:
--   Rosser--Schoenfeld (1962), Theorem 4, eq. (3.14): the finite range $1420 \le t \le 10^{8}$
-- statement:
--   **Rosser--Schoenfeld (1962), Theorem 4, eq. (3.14), finite range.** Let $\theta(t)=\sum_{p\le t}\log p$ over primes $p$. For every real $t$ with
--
--   $$1420 \;\le\; t \;\le\; 10^{8},$$
--
--   one has
--
--   $$t\left(1-\frac{1}{2\log t}\right)\;<\;\theta(t).$$
--
--   This is inequality (3.14) of Rosser and Schoenfeld, *Approximate formulas for some functions of prime numbers*, Illinois J. Math. 6 (1962), 64--94, Theorem 4 (printed p. 70), restricted to the range $1420 \le t \le 10^{8}$.
--
--   **Why this range is the floor.** Above $10^{8}$ the bound follows analytically from the published two-sided estimate `TaoFivePrimes.schoenfeld_psi_error_large`, $|\psi(t)-t|\le t/(40\log t)$, together with Mathlib's `Chebyshev.psi_sub_theta_le`; the threshold $10^{8}$ is the hypothesis of that input and cannot be lowered without replacing it. Below $1420$ the sharper elementary bound $t-2\sqrt t<\theta(t)$ is available as the proved platform theorem `TaoFivePrimes.rosser_schoenfeld_theta_lower_finite`. So $(1420,10^{8}]$ is exactly the finite computation that the analytic method cannot reach, and this node isolates it.
--
--   **What a proof needs, and what does *not* work.** This is a finite computation, not analysis: $\theta$ is non-decreasing, so it suffices to cover $(1420,10^{8}]$ by finitely many intervals and, for each, to certify a lower bound on $\theta$ at the left endpoint exceeding $t(1-1/(2\log t))$ at the right endpoint. The smaller range $255\le t\le 1420$ already has such a certificate (the proved node `TaoFivePrimes.rosser_schoenfeld_theta_lower_finite`).
--
--   However, the technique used for the neighbouring $\psi$ bounds does **not** transfer. That technique certifies $\psi$ *from above* via `Chebyshev.psi_eq_log_lcmUpto`: it exhibits an integer $k$ with `Nat.lcmUpto n ≤ 2^k` and lets the kernel verify the comparison by computation, which is why the `TaoFivePrimes.rosser_psi_certificate_*` family reaches $10^{8}$. Here a **lower** bound on $\theta$ is needed, and $\theta$ is the logarithm of a primorial, not of an lcm, so there is no small integer to exhibit. A certified lower bound for $\theta$ on $(1420,10^{8}]$ therefore needs a different mechanism, or an explicit certificate for the logarithms of all primes up to $10^{8}$ (about $5.7\times 10^{6}$ terms).
--
--   **Formalization Note** `Chebyshev.theta` is Mathlib's $\theta$ function on $\mathbb{R}$. This statement is a range restriction of `TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_mid`; it is a formalization choice of the reduction of that node, not a separately numbered statement in the source.
-- source:
--   J. B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois Journal of Mathematics 6 (1962), 64--94, Theorem 4, printed p. 70, eq. (3.14). Used in T. Tao, Every odd number greater than 1 is the sum of at most five primes, arXiv:1201.6656v4, Section 9, p. 89, to build the parameter y of Lemma 15. The range split at 10^8 is a formalization choice of this reduction: 10^8 is the hypothesis threshold of the published analytic input TaoFivePrimes.schoenfeld_psi_error_large, so it is the natural floor of the finite obligation.

import Mathlib.NumberTheory.Chebyshev

namespace TaoFivePrimes

theorem rosser_schoenfeld_theta_lower_analytic_finite (t : ℝ) (h1 : 1420 ≤ t)
    (h2 : t ≤ 10 ^ 8) :
    t * (1 - 1 / (2 * Real.log t)) < Chebyshev.theta t := by sorry

end TaoFivePrimes
