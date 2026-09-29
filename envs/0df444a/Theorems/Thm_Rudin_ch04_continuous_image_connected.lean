-- Prove2me | Theorems.Thm_Rudin_ch04_continuous_image_connected
-- name    : Rudin.ch04_continuous_image_connected
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T22:11:26.370989+00:00
-- url     : https://prove2.me/theorems/4960d5a4-4b8a-4f7b-81db-734614fac029
-- title:
--   Theorem 4.22 — continuous images of connected sets
-- statement:
--   If $E$ is a connected subset of a metric space $X$ and $f$ is continuous on $E$, then $f(E)$ is connected.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 4, p. 93, Theorem 4.22

import Mathlib
import Definitions.Def_Rudin_ch04_continuity

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 4.22: the continuous image of a connected set is connected. -/
theorem ch04_continuous_image_connected {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) (hE : IsPreconnected E) (hf : ContinuousOn f E) :
    IsPreconnected (f '' E) := by sorry

end Rudin
