-- Prove2me | Theorems.Thm_Rudin_ch04_continuity_iff_limit
-- name    : Rudin.ch04_continuity_iff_limit
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T19:56:59.594265+00:00
-- url     : https://prove2.me/theorems/fa00863b-7a56-45e2-922a-9afdd9cc6942
-- title:
--   Theorem 4.6 — continuity via limits
-- statement:
--   Let $f$ map $E \subseteq X$ into $Y$, let $p \in E$ and suppose $p$ is a limit point of $E$. Then $f$ is continuous at $p$ relative to $E$ if and only if $f(x) \to f(p)$ as $x \to p$ through points of $E$ other than $p$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 4, p. 86, Definition 4.5 and Theorem 4.6

import Mathlib
import Definitions.Def_Rudin_ch02_topology

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 4.6: if `p` is a limit point of `E` and `p ∈ E`, then `f` is continuous at
`p` relative to `E` if and only if `f x → f p` as `x → p` through the points of `E` other
than `p`. -/
theorem ch04_continuity_iff_limit {X Y : Type*} [MetricSpace X] [MetricSpace Y] (E : Set X)
    (f : X → Y) (p : X) (hp : p ∈ E) (hlim : IsLimitPoint p E) :
    ContinuousWithinAt f E p ↔ Tendsto f (𝓝[E \ {p}] p) (𝓝 (f p)) := by sorry

end Rudin
