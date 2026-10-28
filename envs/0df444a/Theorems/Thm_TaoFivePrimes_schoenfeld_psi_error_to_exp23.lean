-- Prove2me | Theorems.Thm_TaoFivePrimes_schoenfeld_psi_error_to_exp23
-- name    : TaoFivePrimes.schoenfeld_psi_error_to_exp23
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T16:19:17.212438+00:00
-- url     : https://prove2.me/theorems/130b2286-d853-4898-aff9-f4c76fa46400
-- title:
--   Two-sided Chebyshev psi error from 10^8 to exp(23)
-- statement:
--   Let $\psi(y)=\sum_{n\le y}\Lambda(n)$ be the second Chebyshev function. For every real $y$ in the bounded interval $10^8\le y<e^{23}$,
--
--   $$|\psi(y)-y|\le \frac{y}{40\log y}.$$
--
--   This is the bounded-range portion of the explicit Chebyshev estimate used in Tao’s Lemma 4.3. The endpoints are included at $10^8$ and excluded at $e^{23}$; no Riemann hypothesis is assumed.
-- source:
--   Terence Tao, Every odd number greater than 1 is the sum of at most five primes, arXiv:1201.6656v4, Section 4, proof of Lemma 4.3, https://arxiv.org/html/1201.6656v4#S4, citing J. B. Rosser and L. Schoenfeld, Sharper bounds for the Chebyshev functions theta(x) and psi(x), Math. Comp. 29 (1975), Theorem 7. This is the restriction to 10^8 ≤ y < exp(23) of the estimate used there.

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem TaoFivePrimes.schoenfeld_psi_error_to_exp23 (y : ℝ) (hy : 10 ^ 8 ≤ y) (hupper : y < Real.exp 23) : |Chebyshev.psi y - y| ≤ y / (40 * Real.log y) := by sorry
