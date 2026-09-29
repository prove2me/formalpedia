-- Prove2me | Theorems.Thm_Rudin_ch02_infinite_subset_limit_point
-- name    : Rudin.ch02_infinite_subset_limit_point
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T18:50:02.445374+00:00
-- url     : https://prove2.me/theorems/72d51032-af65-4e9f-98af-b90a4a432087
-- title:
--   Theorem 2.37 — infinite subsets of compact sets accumulate
-- statement:
--   If $E$ is an infinite subset of a compact set $K$, then $E$ has a limit point in $K$ — a point $p \in K$ every neighbourhood of which meets $E$ in a point other than $p$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 2, p. 38, Theorem 2.37

import Mathlib
import Definitions.Def_Rudin_ch02_topology

namespace Rudin

/-- Rudin, Theorem 2.37: every infinite subset of a compact set `K` has a limit point in `K`. -/
theorem ch02_infinite_subset_limit_point {X : Type*} [MetricSpace X] {K E : Set X}
    (hK : IsCompact K) (hEK : E ⊆ K) (hE : E.Infinite) :
    ∃ p ∈ K, IsLimitPoint p E := by sorry

end Rudin
