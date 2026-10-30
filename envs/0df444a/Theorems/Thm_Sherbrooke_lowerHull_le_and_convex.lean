-- Prove2me | Theorems.Thm_Sherbrooke_lowerHull_le_and_convex
-- name    : Sherbrooke.lowerHull_le_and_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:23:03.514638+00:00
-- url     : https://prove2.me/theorems/5126ac9e-ffb1-4828-8aa0-f04d22d68a0b
-- title:
--   $\Xi'\le\Xi$ and $\Xi'$ is convex
-- statement:
--   Let $\Xi:\mathbb N\to\mathbb R$ be bounded below and let $\Xi'$ be its convexified function (the lower boundary of the convex hull of $\Xi$). Then
--
--   1. $\Xi'(m)\le\Xi(m)$ for every $m\in\mathbb N$, and
--   2. $\Xi'$ is convex on $\mathbb N$: for every $m$,
--
--   $$
--   \Xi'(m+1)-\Xi'(m)\ \le\ \Xi'(m+2)-\Xi'(m+1).
--   $$
--
--   These are the two properties Sherbrooke's definition of $\Xi_i'$ asserts ("lies on the boundary of the convex hull", "decreased to the point of convexity", "$\Xi_i'(m_i)\le\Xi_i(m_i)$") and that the proof of the Appendix Theorem uses ("Since the function $\Xi_i'$ is convex").
--
--   Differences from the source:
--
--   - generalization: Ξ_i monotonic decreasing (standing hypothesis) → hypothesis dropped; reason: this step does not use it; the statement specializes to the source's setting by adding it
--   - encoding: Ξ_i′ defined on the boundary of the convex hull of Ξ_i with Ξ_i′ ≤ Ξ_i → lowerHull Ξ m, the supremum of a m + b over all affine minorants k ↦ a k + b of Ξ on ℕ; reason: on ℕ this is the same function: the lower boundary of the convex hull of the points (k, Ξ(k)), equal to the greatest discretely convex minorant
--   - encoding: finite lower bound → BddBelow (Set.range Ξ); reason: same instances
--   - encoding: Ξ_i′ convex → forward differences of Ξ′ nondecreasing on ℕ; reason: discrete convexity of a sequence; same instances
-- source:
--   Sherbrooke, METRIC: A Multi-Echelon Technique for Recoverable Item Control, Operations Research 16 (1968), doi:10.1287/opre.16.1.122, unnumbered, pp. 135–136 (Ξ_i′ on the boundary of the convex hull, decreased to the point of convexity); used in the Appendix, proof of the Theorem, p. 140

import Mathlib
import Definitions.Def_Sherbrooke_lowerHull

namespace Sherbrooke

/-- **M1: `Ξ′` lies below `Ξ` and is convex.** Sherbrooke, *METRIC*, Operations Research 16
(1968), unnumbered, pp. 135–136: "Let us define a new function Ξ_i′(m) which lies on the boundary
of the convex hull of Ξ_i(m). In other words at any point where Ξ_i(m) is not convex the function
is decreased to the point of convexity in forming the new function Ξ_i′(m)." Used in the proof of
the Appendix Theorem, p. 140: "Since the function Ξ_i′ is convex".

If `Ξ : ℕ → ℝ` is bounded below, then `lowerHull Ξ ≤ Ξ` pointwise and `lowerHull Ξ` is
discretely convex: its forward differences are nondecreasing.

**Formalization Note.** Discrete convexity on `ℕ` is
`Ξ′(m+1) − Ξ′(m) ≤ Ξ′(m+2) − Ξ′(m+1)` for all `m`. The paper's standing hypothesis that `Ξ` is
monotonic decreasing is not needed for this step and is dropped (a generalization). -/
theorem lowerHull_le_and_convex (Ξ : ℕ → ℝ) (hbdd : BddBelow (Set.range Ξ)) :
    (∀ m : ℕ, lowerHull Ξ m ≤ Ξ m) ∧
      ∀ m : ℕ, lowerHull Ξ (m + 1) - lowerHull Ξ m ≤
        lowerHull Ξ (m + 2) - lowerHull Ξ (m + 1) := by sorry

end Sherbrooke
