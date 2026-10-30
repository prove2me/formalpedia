-- Prove2me | Theorems.Thm_Sherbrooke_lowerHull_secant_of_lt
-- name    : Sherbrooke.lowerHull_secant_of_lt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:26:39.158259+00:00
-- url     : https://prove2.me/theorems/bce102c2-c37d-4520-9203-3d3ae174b5e1
-- title:
--   Where $\Xi$ was decreased, $\Xi'$ lies on a secant
-- statement:
--   Let $\Xi:\mathbb N\to\mathbb R$ be nonincreasing and bounded below, and let $\Xi'$ be its convexified function. If $m$ is a point at which $\Xi$ was decreased, $\Xi'(m)<\Xi(m)$, then $m\ge1$ and $\Xi'$ is affine across $m$:
--
--   $$
--   \Xi'(m+1)-\Xi'(m)\ =\ \Xi'(m)-\Xi'(m-1).
--   $$
--
--   This is the step of the Appendix proof showing that such an "artificial point" cannot satisfy (12), whose two lines would then contradict each other.
--
--   Differences from the source:
--
--   - reading: any point m_i at which Ξ_i was decreased to form Ξ_i′ → a point m with Ξ′(m) < Ξ(m); reason: Ξ′ ≤ Ξ everywhere, so 'decreased' means strictly below
--   - reading: the secant equation, which refers to Ξ_i′(m_i − 1) → the conclusion also asserts 1 ≤ m; reason: the equation needs m − 1 ∈ ℕ; the first point is never decreased (Ξ′(0) = Ξ(0)), so this is part of what the step proves
--   - reading: monotonic decreasing → Antitone (nonincreasing); reason: the more general of the two readings; p. 136 justifies monotonicity only as 'cannot exceed'
--   - encoding: Ξ_i′ defined on the boundary of the convex hull of Ξ_i with Ξ_i′ ≤ Ξ_i → lowerHull Ξ m, the supremum of a m + b over all affine minorants k ↦ a k + b of Ξ on ℕ; reason: on ℕ this is the same function: the lower boundary of the convex hull of the points (k, Ξ(k)), equal to the greatest discretely convex minorant
--   - encoding: finite lower bound → BddBelow (Set.range Ξ); reason: same instances
-- source:
--   Sherbrooke, METRIC: A Multi-Echelon Technique for Recoverable Item Control, Operations Research 16 (1968), doi:10.1287/opre.16.1.122, Appendix, proof of the Theorem, p. 140 ("Consider any point m_i at which Ξ_i was decreased to form Ξ_i′. The value of Ξ_i′(m_i) lies on a secant line so that Ξ_i′(m_i + 1) − Ξ_i′(m_i) = Ξ_i′(m_i) − Ξ_i′(m_i − 1).")

import Mathlib
import Definitions.Def_Sherbrooke_lowerHull

namespace Sherbrooke

/-- **M7: at a point where `Ξ` was decreased, `Ξ′` lies on a secant.** Sherbrooke, *METRIC*,
Operations Research 16 (1968), Appendix, proof of the Theorem, p. 140: "Consider any point m_i at
which Ξ_i was decreased to form Ξ_i′. The value of Ξ_i′(m_i) lies on a secant line so that
Ξ_i′(m_i + 1) − Ξ_i′(m_i) = Ξ_i′(m_i) − Ξ_i′(m_i − 1)."

If `Ξ : ℕ → ℝ` is nonincreasing and bounded below and `Ξ′(m) < Ξ(m)` (with `Ξ′ = lowerHull Ξ`),
then `m ≥ 1` and `Ξ′(m + 1) − Ξ′(m) = Ξ′(m) − Ξ′(m − 1)`.

**Formalization Note.** The conjunct `1 ≤ m` (equivalently `Ξ′(0) = Ξ(0)`) is part of the
conclusion, not a hypothesis: the page's secant formula refers to `m_i − 1`, and the first point
is never decreased. Under it the natural-number subtraction `m - 1` is the honest predecessor. -/
theorem lowerHull_secant_of_lt (Ξ : ℕ → ℝ) (hanti : Antitone Ξ)
    (hbdd : BddBelow (Set.range Ξ)) (m : ℕ) (hlt : lowerHull Ξ m < Ξ m) :
    1 ≤ m ∧ lowerHull Ξ (m + 1) - lowerHull Ξ m = lowerHull Ξ m - lowerHull Ξ (m - 1) := by sorry

end Sherbrooke
