-- Prove2me | Theorems.Thm_Rudin_ch04_continuous_image_compact
-- name    : Rudin.ch04_continuous_image_compact
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T20:06:13.77859+00:00
-- url     : https://prove2.me/theorems/8eb29286-0b57-4762-a211-923cb9e77588
-- title:
--   Theorem 4.14 — continuous images of compact sets
-- statement:
--   If $K$ is a compact subset of a metric space $X$ and $f$ is continuous on $K$, then $f(K)$ is compact.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 4, p. 89, Theorem 4.14

import Mathlib
import Definitions.Def_Rudin_ch04_continuity

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 4.14: the continuous image of a compact set is compact. -/
theorem ch04_continuous_image_compact {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (K : Set X) (hK : IsCompact K) (hf : ContinuousOn f K) :
    IsCompact (f '' K) := by sorry

end Rudin
