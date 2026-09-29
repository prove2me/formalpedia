-- Prove2me | Theorems.Thm_Rudin_ch03_dirichlet_test
-- name    : Rudin.ch03_dirichlet_test
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T19:19:38.086264+00:00
-- url     : https://prove2.me/theorems/64d576c6-6b99-4a57-918d-4825d24df016
-- title:
--   Theorem 3.42 — Dirichlet's test
-- statement:
--   Suppose the partial sums of $\sum a_n$ form a bounded sequence, $b_0 \ge b_1 \ge b_2 \ge \cdots$, and $b_n \to 0$. Then $\sum a_n b_n$ converges.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 3, p. 70, Theorems 3.41 and 3.42

import Mathlib
import Definitions.Def_Rudin_ch03_series

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 3.42 (Dirichlet's test): if the partial sums of `∑ aₙ` form a bounded
sequence, and `b₀ ≥ b₁ ≥ b₂ ≥ ⋯` tends to `0`, then `∑ aₙ bₙ` converges. -/
theorem ch03_dirichlet_test (a : ℕ → ℂ) (b : ℕ → ℝ)
    (hA : ∃ M : ℝ, ∀ n, ‖partialSum a n‖ ≤ M)
    (hb : ∀ n, b (n + 1) ≤ b n) (hb0 : Tendsto b atTop (𝓝 0)) :
    SeriesConverges (fun n => a n * (b n : ℂ)) := by sorry

end Rudin
