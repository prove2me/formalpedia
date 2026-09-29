-- Prove2me | Theorems.Thm_Rudin_ch04_continuous_iff_preimage_open
-- name    : Rudin.ch04_continuous_iff_preimage_open
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T20:04:35.081335+00:00
-- url     : https://prove2.me/theorems/c468aa79-4ec9-440f-ba2b-5573d8ce821b
-- title:
--   Theorem 4.8 — continuity by preimages of open sets
-- statement:
--   A mapping $f$ of a metric space $X$ into a metric space $Y$ is continuous if and only if $f^{-1}(V)$ is open in $X$ for every open $V \subseteq Y$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 4, p. 86, Theorem 4.8

import Mathlib
import Definitions.Def_Rudin_ch04_continuity

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 4.8: a mapping `f` of a metric space `X` into a metric space `Y` is
continuous if and only if the preimage of every open subset of `Y` is open in `X`. -/
theorem ch04_continuous_iff_preimage_open {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) : Continuous f ↔ ∀ V : Set Y, IsOpen V → IsOpen (f ⁻¹' V) := by sorry

end Rudin
