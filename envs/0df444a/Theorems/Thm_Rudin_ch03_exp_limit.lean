-- Prove2me | Theorems.Thm_Rudin_ch03_exp_limit
-- name    : Rudin.ch03_exp_limit
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T19:07:47.581739+00:00
-- url     : https://prove2.me/theorems/f96741c0-d401-4083-981b-a8b2e82c33b3
-- title:
--   Theorems 3.30-3.31 — two descriptions of $e$
-- statement:
--   The series $\sum_{n \ge 0} 1/n!$ converges to $e$, and $(1 + 1/n)^n \to e$ as $n \to \infty$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 3, pp. 63-64, Definition 3.30 and Theorem 3.31

import Mathlib
import Definitions.Def_Rudin_ch03_series

open Filter Topology

namespace Rudin

/-- Rudin, Definition 3.30 and Theorem 3.31: the number `e` is the sum of the series
`∑ 1/n!`, and it is also the limit of `(1 + 1/n)ⁿ`. -/
theorem ch03_exp_limit :
    SeriesConvergesTo (fun n : ℕ => (1 : ℝ) / n.factorial) (Real.exp 1) ∧
    Tendsto (fun n : ℕ => (1 + 1 / (n : ℝ)) ^ n) atTop (𝓝 (Real.exp 1)) := by sorry

end Rudin
