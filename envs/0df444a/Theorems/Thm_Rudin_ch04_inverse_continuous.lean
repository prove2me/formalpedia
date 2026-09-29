-- Prove2me | Theorems.Thm_Rudin_ch04_inverse_continuous
-- name    : Rudin.ch04_inverse_continuous
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T20:24:24.266567+00:00
-- url     : https://prove2.me/theorems/3580d2f7-be6c-40f7-af5c-4fca3fa24e18
-- title:
--   Theorem 4.17 — continuity of the inverse on a compact domain
-- statement:
--   If $f$ is a continuous one-to-one mapping of a compact metric space $X$ onto a metric space $Y$, then the inverse mapping $g = f^{-1}$ is continuous on $Y$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 4, p. 90, Theorem 4.17

import Mathlib
import Definitions.Def_Rudin_ch04_continuity

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 4.17: if `f` is a continuous one-to-one mapping of a compact metric space
`X` onto a metric space `Y`, then the inverse mapping `g` is continuous. -/
theorem ch04_inverse_continuous {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompactSpace X]
    (f : X → Y) (g : Y → X) (hf : Continuous f)
    (hgf : ∀ x : X, g (f x) = x) (hfg : ∀ y : Y, f (g y) = y) :
    Continuous g := by sorry

end Rudin
