-- Prove2me | Theorems.Thm_Rudin_ch03_ratio_test
-- name    : Rudin.ch03_ratio_test
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-09-12T19:13:18.259985+00:00
-- url     : https://prove2.me/theorems/5a2ed5a2-58e0-4701-ac96-bad02f00f6c4
-- title:
--   Theorem 3.34 — ratio test
-- statement:
--   The series $\sum a_n$ converges if $\limsup_n |a_{n+1}/a_n| < 1$, and diverges if there is an $N$ such that for all $n \ge N$ the terms are nonzero and $|a_{n+1}| \ge |a_n|$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 3, p. 66, Theorem 3.34

import Mathlib
import Definitions.Def_Rudin_ch03_series

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 3.34 (ratio test): `∑ aₙ` converges if `limsup ‖aₙ₊₁ / aₙ‖ < 1`, and
diverges if there is an `N` with `‖aₙ₊₁‖ ≥ ‖aₙ‖` for all `n ≥ N` and `aₙ ≠ 0` there. -/
theorem ch03_ratio_test (a : ℕ → ℂ) :
    (limsup (fun n => ((‖a (n + 1)‖ / ‖a n‖ : ℝ) : EReal)) atTop < 1 → SeriesConverges a) ∧
    ((∃ N, ∀ n ≥ N, a n ≠ 0 ∧ ‖a n‖ ≤ ‖a (n + 1)‖) → ¬ SeriesConverges a) := by sorry

end Rudin
