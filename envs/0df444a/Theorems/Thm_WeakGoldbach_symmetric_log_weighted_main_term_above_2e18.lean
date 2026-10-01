-- Prove2me | Theorems.Thm_WeakGoldbach_symmetric_log_weighted_main_term_above_2e18
-- name    : WeakGoldbach.symmetric_log_weighted_main_term_above_2e18
-- status  : Open
-- author  : @webmh
-- created : 2026-09-11T23:13:50.232444+00:00
-- url     : https://prove2.me/theorems/2767c7e0-c374-45c8-b2d7-ab3189fde3cd
-- title:
--   Open weighted lower-bound problem for symmetric Goldbach pairs
-- statement:
--   Let $m$ be a natural number with $m>2\cdot10^{18}$, and put
--   $$
--   \mathcal P_m=\{t\in\mathbb N:0\le t<m-1,\ m-t\text{ and }m+t\text{ are prime}\},
--   \qquad S(2m)=\prod_{\substack{p\mid2m\\p>2}}\frac{p-1}{p-2}.
--   $$
--   The proposed lower bound is
--   $$
--   \sum_{t\in\mathcal P_m}\log(m-t)\log(m+t)\ \ge\ S(2m)m.
--   $$
--   This is an **open sufficient analytic problem**, introduced for the logarithmic-weight-removal reduction of `WeakGoldbach.symmetric_pair_main_term_above_2e18`. It is not an established theorem, and no explicit error estimate or verification of the cutoff is supplied here. The exact cutoff is inherited from that target, not from a published asymptotic theorem.
--
--   The source below motivates using logarithmic weights but states an asymptotic conjecture for the von Mangoldt convolution, which includes prime powers and counts ordered pairs. The present statement instead counts only prime pairs, with nonnegative offsets and the diagonal counted once. It is an explicit finite-threshold strengthening of that heuristic motivation, not a verbatim restatement or a claimed consequence of an asymptotic with an unspecified cutoff.
--
--   The role of this problem is to isolate a uniform logarithmically weighted estimate for subsequent weight-removal arguments. Its solution would in particular imply binary Goldbach above the specified threshold.
-- source:
--   Prove2Me target https://prove2.me/theorems/dda1eab7-cf9d-4c6b-9db9-2339f4f6f944 (exact threshold and local factor). Weighted-method motivation only: Thi Thu Nguyen, Generalized Goldbach Functions and their Asymptotics (2024), printed p. 9, equations (1.2)-(1.3), Conjecture 1.0.1, https://pro.univ-lille.fr/fileadmin/user_upload/pages_pros/gautami_bhowmik/Encadrements/Nguyen_7nov.pdf . This proposed explicit prime-only lower bound is NOT asserted by that source.

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

theorem WeakGoldbach.symmetric_log_weighted_main_term_above_2e18
    (m : ℕ) (hm : 2 * 10 ^ 18 < m) :
    (∏ p ∈ (2 * m).primeFactors.filter (2 < ·), ((p : ℝ) - 1) / ((p : ℝ) - 2))
      * (m : ℝ) ≤
    ∑ t ∈ (Finset.range (m - 1)).filter
      (fun t => Nat.Prime (m - t) ∧ Nat.Prime (m + t)),
      Real.log (m - t : ℕ) * Real.log (m + t : ℕ) := by sorry
