-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_analytic_mid_lower
-- name    : TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_mid_lower
-- status  : Open
-- author  : @Yuxuan Xu
-- created : 2026-09-24T12:42:47.923054+00:00
-- url     : https://prove2.me/theorems/fa58620e-0727-4e9a-9ea0-8e7318b6aef5
-- title:
--   Rosser--Schoenfeld (1962), Theorem 4, eq. (3.14): the finite range $1420 \le t \le 10^{9}$
-- statement:
--   **Rosser--Schoenfeld (1962), Theorem 4, eq. (3.14), finite part of the middle range.** Let $\theta(t)=\sum_{p\le t}\log p$ over primes $p$. For every real $t$ with
--
--   $$1420 \;\le\; t \;\le\; 10^{9},$$
--
--   one has
--
--   $$t\left(1-\frac{1}{2\log t}\right)\;<\;\theta(t).$$
--
--   This is the finite part of inequality (3.14) of Rosser and Schoenfeld, *Approximate formulas for some functions of prime numbers*, Illinois J. Math. 6 (1962), 64--94, Theorem 4 (printed p. 70).
--
--   **Why this node exists.** The sibling theorem `TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_mid` carries the whole range $1420\le t\le10^{10}$ as a single finite obligation, and above $10^{10}$ the published node `TaoFivePrimes.schoenfeld_psi_error_large` already forces (3.14). Splitting the middle range at $10^{9}$ makes the finite obligation ten times smaller and leaves the analytic part entirely to the $\psi$ input: on $t\ge10^{9}$ the two-sided estimate $|\psi(t)-t|\le t/(40\log t)$ together with Mathlib's `Chebyshev.psi_sub_theta_le`, $\psi(t)-\theta(t)\le 2\sqrt t\log t$, reduces (3.14) to the elementary comparison $(19/40)\sqrt t>2(\log t)^2$, which holds on that range because $\log t\le 16\,t^{1/16}$ (four nested square roots) and $\sqrt[8]{t}\ge13.3$.
--
--   **Why $10^{9}$ and not $10^{8}$.** The threshold is a seam, not a feature: $10^{9}$ is a round constant for which $(19/40)\sqrt t>2(\log t)^2$ is still provable from the explicit logarithmic bound used in the sibling reduction. The genuinely finite range $1420<t\le10^{9}$ is what a future certificate has to cover.
--
--   **Formalization Note** `Chebyshev.theta` is Mathlib's $\theta$ function on $\mathbb{R}$. The statement is a range restriction of the existing platform theorem `TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_mid`; no new mathematics is claimed beyond the range split, which is a formalization choice and not a separately numbered statement in the source.
-- source:
--   J. B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois Journal of Mathematics 6 (1962), 64--94, Theorem 4, printed p. 70, eq. (3.14). Used in T. Tao, Every odd number greater than 1 is the sum of at most five primes, arXiv:1201.6656v4, Section 9, p. 89, to build the parameter y of Lemma 15. The range split at 10^9 is a formalization choice of this reduction: it is the largest round threshold at which the elementary comparison of the sibling reduction is still available, and it makes the remaining finite obligation as small as the published psi input allows.

import Mathlib.NumberTheory.Chebyshev

namespace TaoFivePrimes

theorem rosser_schoenfeld_theta_lower_analytic_mid_lower (t : ℝ) (h1 : 1420 ≤ t)
    (h2 : t ≤ 10 ^ 9) :
    t * (1 - 1 / (2 * Real.log t)) < Chebyshev.theta t := by sorry

end TaoFivePrimes
