-- Prove2me | Theorems.Thm_SherbrookeMetric_ConvexHull_hull_optimal
-- name    : SherbrookeMetric.ConvexHull.hull_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:53:07.599585+00:00
-- url     : https://prove2.me/theorems/1018ee70-d73c-41b7-992d-5e60f97ebde8
-- title:
--   Appendix — the marginal solution minimizes the convexified item cost
-- statement:
--   Let $\Xi:\mathbb N\to\mathbb R$ be nonincreasing and bounded below, let $H$ be its lower convex hull, and let $c>0$. If $\bar m$ satisfies the marginal conditions (12), then for every stock level $m$,
--
--   $$c\bar m+H(\bar m)\le cm+H(m).$$
--
--   This is optimality for the convexified, single-item objective. The separate contact result is needed to transfer the conclusion to the original $\Xi$.
-- source:
--   Sherbrooke, METRIC: A Multi-Echelon Technique for Recoverable Item Control, Oper. Res. 16 (1968), p. 140, Appendix, proof of the THEOREM (It is clear that if m-bar_i exist that satisfy equation (12)); DOI 10.1287/opre.16.1.122

import Mathlib
import Definitions.Def_SherbrookeMetric_ConvexHull_LowerHull
import Definitions.Def_SherbrookeMetric_ConvexHull_MarginalConditions

namespace SherbrookeMetric.ConvexHull

/-- Appendix, proof of the THEOREM, p. 140: (12) minimizes the objective
formed with the lower hull for one item. -/
theorem hull_optimal (Ξ : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (hanti : Antitone Ξ) (hbdd : BddBelow (Set.range Ξ))
    (mbar : ℕ) (hmc : MarginalConditions c (lowerHull Ξ) mbar) :
    ∀ m : ℕ, c * (mbar : ℝ) + lowerHull Ξ mbar ≤
      c * (m : ℝ) + lowerHull Ξ m := by sorry

end SherbrookeMetric.ConvexHull
