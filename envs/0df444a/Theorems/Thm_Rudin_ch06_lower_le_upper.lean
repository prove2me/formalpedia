-- Prove2me | Theorems.Thm_Rudin_ch06_lower_le_upper
-- name    : Rudin.ch06_lower_le_upper
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T20:07:04.550448+00:00
-- url     : https://prove2.me/theorems/77b08a17-cba7-4cf9-bcb2-b90994a8b171
-- title:
--   Theorem 6.5 — the lower integral is at most the upper integral
-- statement:
--   For a bounded $f$ and a monotonically increasing $\alpha$ on $[a,b]$, $\underline{\int_a^b} f\,d\alpha \le \overline{\int_a^b} f\,d\alpha$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 6, p. 123, Theorem 6.5

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 6.5: for a bounded `f` and a monotonically increasing `α`, the lower
integral never exceeds the upper integral. -/
theorem ch06_lower_le_upper (a b : ℝ) (hab : a ≤ b) (f α : ℝ → ℝ)
    (hα : MonotoneOn α (Set.Icc a b)) (hf : ∃ M, ∀ x ∈ Set.Icc a b, |f x| ≤ M) :
    lowerIntegral a b f α ≤ upperIntegral a b f α := by sorry

end Rudin
