-- Prove2me | Theorems.Thm_Sherbrooke_lowerHull_diff_tendsto_zero
-- name    : Sherbrooke.lowerHull_diff_tendsto_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:24:49.555868+00:00
-- url     : https://prove2.me/theorems/7bee55c0-a6ef-4925-8f89-db608aca2d43
-- title:
--   $\Xi'$ is decreasing and bounded below; its differences tend to $0$
-- statement:
--   Let $\Xi:\mathbb N\to\mathbb R$ be nonincreasing and bounded below, and let $\Xi'$ be its convexified function. Then
--
--   1. $\Xi'$ is nonincreasing,
--   2. $\Xi'$ is bounded below, and
--   3. its forward differences vanish:
--
--   $$
--   \lim_{m\to\infty}\bigl(\Xi'(m+1)-\Xi'(m)\bigr)=0 .
--   $$
--
--   The proof of the Appendix Theorem invokes "the fact that a monotonically decreasing sequence bounded below has a limit" for $\Xi'$; this is what makes the first inequality of (12) attainable for a positive cost.
--
--   Differences from the source:
--
--   - reading: We use the fact that a monotonically decreasing sequence bounded below has a limit → Ξ′ is nonincreasing and bounded below, and Ξ′(m + 1) − Ξ′(m) → 0; reason: the page names only the fact; this is the fact applied to Ξ′, as the existence step uses it
--   - reading: monotonic decreasing → Antitone (nonincreasing); reason: the more general of the two readings; p. 136 justifies monotonicity only as 'cannot exceed'
--   - encoding: Ξ_i′ defined on the boundary of the convex hull of Ξ_i with Ξ_i′ ≤ Ξ_i → lowerHull Ξ m, the supremum of a m + b over all affine minorants k ↦ a k + b of Ξ on ℕ; reason: on ℕ this is the same function: the lower boundary of the convex hull of the points (k, Ξ(k)), equal to the greatest discretely convex minorant
--   - encoding: finite lower bound → BddBelow (Set.range Ξ); reason: same instances
-- source:
--   Sherbrooke, METRIC: A Multi-Echelon Technique for Recoverable Item Control, Operations Research 16 (1968), doi:10.1287/opre.16.1.122, Appendix, proof of the Theorem, p. 140 ("We use the fact that a monotonically decreasing sequence bounded below has a limit.")

import Mathlib
import Definitions.Def_Sherbrooke_lowerHull

namespace Sherbrooke

/-- **M4: `Ξ′` is decreasing, bounded below, and its differences tend to 0.** Sherbrooke,
*METRIC*, Operations Research 16 (1968), Appendix, proof of the Theorem, p. 140: "We use the fact
that a monotonically decreasing sequence bounded below has a limit."

If `Ξ : ℕ → ℝ` is nonincreasing and bounded below, then `Ξ′ = lowerHull Ξ` is nonincreasing,
bounded below, and `Ξ′(m + 1) − Ξ′(m) → 0` as `m → ∞`.

**Formalization Note.** The page names only the fact about monotone bounded sequences; this
milestone is that fact applied to `Ξ′`, which is how the proof uses it. "Monotonic decreasing" is
read as `Antitone` (nonincreasing). -/
theorem lowerHull_diff_tendsto_zero (Ξ : ℕ → ℝ) (hanti : Antitone Ξ)
    (hbdd : BddBelow (Set.range Ξ)) :
    Antitone (lowerHull Ξ) ∧ BddBelow (Set.range (lowerHull Ξ)) ∧
      Filter.Tendsto (fun m : ℕ => lowerHull Ξ (m + 1) - lowerHull Ξ m) Filter.atTop
        (nhds 0) := by sorry

end Sherbrooke
