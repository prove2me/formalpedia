-- Prove2me | Theorems.Thm_SherbrookeMetric_ConvexHull_lowerHull_spec
-- name    : SherbrookeMetric.ConvexHull.lowerHull_spec
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:52:53.588934+00:00
-- url     : https://prove2.me/theorems/937822cc-b9e7-4782-b9da-5a50ddfed74a
-- title:
--   Appendix — the lower hull is the greatest convex minorant
-- statement:
--   Let $\Xi:\mathbb N\to\mathbb R$ be nonincreasing and bounded below, and let $H$ be its lower convex hull. Then
--
--   $$
--   H\text{ is discretely convex},\qquad H(m)\le\Xi(m)\quad(m\ge0),
--   $$
--
--   and every discretely convex $g$ satisfying $g(m)\le\Xi(m)$ at every stock level also satisfies $g(m)\le H(m)$ everywhere.
--
--   This establishes that the constructed boundary is the largest convex function allowed beneath the original item function. That maximality is needed when the hull is later compared with the original function.
-- source:
--   Sherbrooke, METRIC: A Multi-Echelon Technique for Recoverable Item Control, Oper. Res. 16 (1968), p. 140, Appendix THEOREM (definition of Xi-prime), with pp. 135–136, Generalization of the Objective Function; DOI 10.1287/opre.16.1.122

import Mathlib
import Definitions.Def_SherbrookeMetric_ConvexHull_LowerHull

namespace SherbrookeMetric.ConvexHull

/-- Appendix, p. 140, and the lower-hull construction on pp. 135–136. -/
theorem lowerHull_spec (Ξ : ℕ → ℝ) (hanti : Antitone Ξ)
    (hbdd : BddBelow (Set.range Ξ)) :
    DiscreteConvex (lowerHull Ξ) ∧
      (∀ m : ℕ, lowerHull Ξ m ≤ Ξ m) ∧
      (∀ g : ℕ → ℝ, DiscreteConvex g →
        (∀ m : ℕ, g m ≤ Ξ m) → ∀ m : ℕ, g m ≤ lowerHull Ξ m) := by sorry

end SherbrookeMetric.ConvexHull
