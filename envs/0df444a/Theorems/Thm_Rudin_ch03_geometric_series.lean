-- Prove2me | Theorems.Thm_Rudin_ch03_geometric_series
-- name    : Rudin.ch03_geometric_series
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T19:04:25.982865+00:00
-- url     : https://prove2.me/theorems/1c46f4d3-e5c0-4bd5-912b-4295f9d2e8c9
-- title:
--   Theorem 3.26 — the geometric series
-- statement:
--   For $0 \le x < 1$, $\sum_{n \ge 0} x^n$ converges to $1/(1-x)$; for $x \ge 1$ the series diverges.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 3, p. 61, Theorem 3.26

import Mathlib
import Definitions.Def_Rudin_ch03_series

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 3.26: if `0 ≤ x < 1` then the geometric series `∑ xⁿ` converges to
`1 / (1 - x)`, and if `x ≥ 1` it diverges. -/
theorem ch03_geometric_series (x : ℝ) (hx : 0 ≤ x) :
    (x < 1 → SeriesConvergesTo (fun n => x ^ n) (1 / (1 - x))) ∧
    (1 ≤ x → ¬ SeriesConverges (fun n => x ^ n)) := by sorry

end Rudin
