-- Prove2me | Theorems.Thm_WeakGoldbach_symmetric_vonMangoldt_lower_bound_above_2e18
-- name    : WeakGoldbach.symmetric_vonMangoldt_lower_bound_above_2e18
-- status  : Open
-- author  : @webmh
-- created : 2026-09-11T23:26:08.420884+00:00
-- url     : https://prove2.me/theorems/55310293-603e-422d-b934-e32fddc6441c
-- title:
--   Open symmetric von Mangoldt lower bound with a prime-power error margin
-- statement:
--   Let $m$ be a natural number with $m>2\cdot10^{18}$. Let $\Lambda$ denote the von Mangoldt function: $\Lambda(p^k)=\log p$ for primes $p$ and integers $k\ge1$, and zero otherwise. Write
--   $$
--   S(2m)=\prod_{\substack{p\mid2m\\p>2}}\frac{p-1}{p-2},\qquad
--   A(m)=\sum_{0\le t<m-1}\Lambda(m-t)\Lambda(m+t).
--   $$
--   The proposed bound is
--   $$
--   A(m)\ge\frac54 S(2m)m.
--   $$
--   This is an **open sufficient conjectural estimate**, not a known consequence of the Hardy–Littlewood conjecture at the stated finite threshold. It is introduced as the remaining analytic obligation in the prime-power-removal reduction of `WeakGoldbach.symmetric_log_weighted_main_term_above_2e18`. The coefficient $5/4$ reserves room for an elementary prime-power error estimate. The cutoff is inherited from that target and has not been established by an explicit circle-method estimate or computation.
--
--   The sum is over nonnegative offsets, includes the diagonal once, and includes prime powers. It is not the ordered convolution from the cited source. The source supplies the von Mangoldt definition and asymptotic motivation only; neither this finite-threshold inequality nor its coefficient is asserted there. Solving this uniform estimate would settle the target's outstanding Goldbach difficulty.
-- source:
--   Original sufficient conjectural estimate for the prime-power-removal reduction of https://prove2.me/theorems/2767c7e0-c374-45c8-b2d7-ab3189fde3cd . Definition and asymptotic motivation only: Thi Thu Nguyen, Generalized Goldbach Functions and their Asymptotics (2024), printed p. 9, equations (1.2)-(1.3), Conjecture 1.0.1; printed p. 10, definition of von Mangoldt; https://pro.univ-lille.fr/fileadmin/user_upload/pages_pros/gautami_bhowmik/Encadrements/Nguyen_7nov.pdf . This source does NOT prove the displayed finite-threshold estimate.

import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

theorem WeakGoldbach.symmetric_vonMangoldt_lower_bound_above_2e18
    (m : ℕ) (hm : 2 * 10 ^ 18 < m) :
    (5 / 4 : ℝ) *
      (∏ p ∈ (2 * m).primeFactors.filter (2 < ·), ((p : ℝ) - 1) / ((p : ℝ) - 2)) *
      (m : ℝ) ≤
    ∑ t ∈ Finset.range (m - 1),
      ArithmeticFunction.vonMangoldt (m - t) * ArithmeticFunction.vonMangoldt (m + t) := by sorry
