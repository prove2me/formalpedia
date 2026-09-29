-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_analytic_mid
-- name    : TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_mid
-- status  : Open
-- author  : @Yuxuan Xu
-- created : 2026-09-18T11:08:24.228449+00:00
-- url     : https://prove2.me/theorems/56cff342-4599-468f-86e6-d25d03d60925
-- title:
--   Rosser--Schoenfeld (1962), Theorem 4, eq. (3.14): the middle range $1420 \le t \le 10^{10}$
-- statement:
--   **Rosser--Schoenfeld (1962), Theorem 4, eq. (3.14), middle range.** Let $\theta$ be the Chebyshev function, $\theta(t)=\sum_{p\le t}\log p$ over primes $p$. For every real $t$ with
--
--   $$1420 \;\le\; t \;\le\; 10^{10},$$
--
--   one has
--
--   $$t\left(1-\frac{1}{2\log t}\right)\;<\;\theta(t).$$
--
--   This is the middle segment of inequality (3.14) of Rosser and Schoenfeld, *Approximate formulas for some functions of prime numbers*, Illinois J. Math. 6 (1962), 64--94, Theorem 4 (printed p. 70): the explicit lower bound for $\theta$ that is valid for every $t\ge 1340$.
--
--   The range here is deliberately finite. The universal statement $t\ge 1340$ is the platform theorem `TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic`; it decomposes into exactly three segments. Below $1420$ the sharper elementary bound $t-2\sqrt t<\theta(t)$ is already available as the proved platform theorem `TaoFivePrimes.rosser_schoenfeld_theta_lower_finite` (Rosser--Schoenfeld, Theorem 4, finite range $255\le t\le 1420$), and above $10^{10}$ the two-sided Chebyshev estimate of the platform input `TaoFivePrimes.schoenfeld_psi_error_large` already forces (3.14), because $\psi(t)-\theta(t)\le 2\sqrt t\log t$ is available in Mathlib as `Chebyshev.psi_sub_theta_le` and $(19/40)\sqrt t>2(\log t)^2$ on that range. What remains, and what this theorem isolates, is the genuinely finite computational range $(1420,10^{10}]$
--
--   **Formalization Note** `Chebyshev.theta` is Mathlib's $\theta$ function on $\mathbb{R}$. The upper endpoint $10^{10}$ is not a source constant: it is the threshold at which the elementary comparison $(19/40)\sqrt t>2(\log t)^2$ becomes provable from $\log t\le 8\,t^{1/8}$, so that the Schoenfeld input can take over. The range $255\le t\le 1420$ of the proved finite node is quoted as-is from the platform.
-- source:
--   J. B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois Journal of Mathematics 6 (1962), 64--94, Theorem 4, printed p. 70, eq. (3.14). Used in T. Tao, Every odd number greater than 1 is the sum of at most five primes, arXiv:1201.6656v4, Section 9, p. 89, to build the parameter y of Lemma 15. The finite range $1420\le t\le 10^{10}$ is a formalization choice of this reduction, made so that the already-proved node `rosser_schoenfeld_theta_lower_finite` covers $t\le 1420$ and the published node `schoenfeld_psi_error_large` covers $t\ge 10^{10}$; it is not a separately numbered statement in the source.

import Mathlib.NumberTheory.Chebyshev

namespace TaoFivePrimes

theorem rosser_schoenfeld_theta_lower_analytic_mid (t : ℝ) (h1 : 1420 ≤ t)
    (h2 : t ≤ 10 ^ 10) :
    t * (1 - 1 / (2 * Real.log t)) < Chebyshev.theta t := by sorry

end TaoFivePrimes
