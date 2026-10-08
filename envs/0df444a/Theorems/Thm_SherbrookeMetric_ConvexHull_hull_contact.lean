-- Prove2me | Theorems.Thm_SherbrookeMetric_ConvexHull_hull_contact
-- name    : SherbrookeMetric.ConvexHull.hull_contact
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:53:09.075327+00:00
-- url     : https://prove2.me/theorems/71d90686-d25f-4009-965e-22408e2edbcd
-- title:
--   Appendix — the marginal solution is a contact point of the lower hull
-- statement:
--   Let $\Xi:\mathbb N\to\mathbb R$ be nonincreasing and bounded below, let $H$ be its lower convex hull, and let $c>0$. If $\bar m$ satisfies (12), then the hull meets the original function at the selected stock level:
--
--   $$H(\bar m)=\Xi(\bar m).$$
--
--   Thus the selected point is not one of the artificially lowered points introduced by convexification. This is the step that makes the convexified optimization rule valid for the original item cost.
-- source:
--   Sherbrooke, METRIC: A Multi-Echelon Technique for Recoverable Item Control, Oper. Res. 16 (1968), pp. 140–141, Appendix, proof of the THEOREM (Consider any point m_i at which Xi_i was decreased); DOI 10.1287/opre.16.1.122

import Mathlib
import Definitions.Def_SherbrookeMetric_ConvexHull_LowerHull
import Definitions.Def_SherbrookeMetric_ConvexHull_MarginalConditions

namespace SherbrookeMetric.ConvexHull

/-- Appendix, proof of the THEOREM, pp. 140–141: a point selected by (12)
is a contact point of the original function and its lower hull. -/
theorem hull_contact (Ξ : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (hanti : Antitone Ξ) (hbdd : BddBelow (Set.range Ξ))
    (mbar : ℕ) (hmc : MarginalConditions c (lowerHull Ξ) mbar) :
    lowerHull Ξ mbar = Ξ mbar := by sorry

end SherbrookeMetric.ConvexHull
