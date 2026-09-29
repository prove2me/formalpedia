-- Prove2me | Theorems.Thm_Rudin_ch03_p_series
-- name    : Rudin.ch03_p_series
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T19:05:52.317545+00:00
-- url     : https://prove2.me/theorems/a9447bc5-43a0-447c-ad0f-d1784fbbfe75
-- title:
--   Theorem 3.28 — the $p$-series
-- statement:
--   The series $\sum_{n \ge 1} n^{-p}$ converges if $p > 1$ and diverges if $p \le 1$. (Indices are shifted by one in the formal statement so that the terms are $(n+1)^{-p}$ for $n \ge 0$.)
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 3, p. 62, Theorem 3.28

import Mathlib
import Definitions.Def_Rudin_ch03_series

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 3.28: the series `∑_{n ≥ 1} n^{-p}` converges if `p > 1` and diverges if
`p ≤ 1`. -/
theorem ch03_p_series (p : ℝ) :
    SeriesConverges (fun n : ℕ => ((n : ℝ) + 1) ^ (-p)) ↔ 1 < p := by sorry

end Rudin
