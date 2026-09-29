-- Prove2me | Theorems.Thm_Rudin_ch02_cover_compact_iff_compact
-- name    : Rudin.ch02_cover_compact_iff_compact
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T18:48:47.719392+00:00
-- url     : https://prove2.me/theorems/cb40f323-9aba-4e49-b6dd-de8843e70e51
-- title:
--   Definition 2.32 — open-cover compactness agrees with the library notion
-- statement:
--   For a subset $K$ of a metric space, Rudin's definition — every open cover of $K$ has a finite subcover — is equivalent to the notion of compactness used in Mathlib.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 2, p. 36, Definitions 2.31 and 2.32

import Mathlib
import Definitions.Def_Rudin_ch02_topology

namespace Rudin

/-- Rudin, Definition 2.32: the open-cover definition of compactness agrees with the notion of
compactness used in Mathlib. -/
theorem ch02_cover_compact_iff_compact {X : Type*} [MetricSpace X] (K : Set X) :
    IsCoverCompact K ↔ IsCompact K := by sorry

end Rudin
