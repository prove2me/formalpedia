-- Prove2me | Theorems.Thm_Rudin_ch02_closed_in_compact
-- name    : Rudin.ch02_closed_in_compact
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T18:49:02.101873+00:00
-- url     : https://prove2.me/theorems/70fe0b92-545a-40c3-99b6-785fb1ec1fb7
-- title:
--   Theorem 2.35 — closed subsets of compact sets are compact
-- statement:
--   If $K$ is compact, $F$ is closed and $F \subseteq K$, then $F$ is compact.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 2, p. 37, Theorem 2.35

import Mathlib

namespace Rudin

/-- Rudin, Theorem 2.35: closed subsets of compact sets are compact. -/
theorem ch02_closed_in_compact {X : Type*} [MetricSpace X] {K F : Set X}
    (hK : IsCompact K) (hF : IsClosed F) (hFK : F ⊆ K) : IsCompact F := by sorry

end Rudin
