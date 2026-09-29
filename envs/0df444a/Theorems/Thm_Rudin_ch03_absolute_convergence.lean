-- Prove2me | Theorems.Thm_Rudin_ch03_absolute_convergence
-- name    : Rudin.ch03_absolute_convergence
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T19:22:24.696674+00:00
-- url     : https://prove2.me/theorems/68fb2f20-f8d0-47b6-bba6-ff5f3ab79fe9
-- title:
--   Theorem 3.45 — absolute convergence implies convergence
-- statement:
--   If $\sum \|a_n\|$ converges then $\sum a_n$ converges.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 3, p. 71, Theorem 3.45

import Mathlib
import Definitions.Def_Rudin_ch03_series

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 3.45: an absolutely convergent series converges. -/
theorem ch03_absolute_convergence (a : ℕ → ℂ) (h : SeriesConvergesAbsolutely a) :
    SeriesConverges a := by sorry

end Rudin
