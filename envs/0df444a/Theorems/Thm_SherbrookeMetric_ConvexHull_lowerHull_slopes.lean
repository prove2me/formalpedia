-- Prove2me | Theorems.Thm_SherbrookeMetric_ConvexHull_lowerHull_slopes
-- name    : SherbrookeMetric.ConvexHull.lowerHull_slopes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:52:52.423242+00:00
-- url     : https://prove2.me/theorems/bb7d4062-6f39-47fc-aff6-ee33b311e82e
-- title:
--   Appendix — the lower hull's marginal changes approach zero
-- statement:
--   Let $\Xi:\mathbb N\to\mathbb R$ be nonincreasing and bounded below, and let $H$ be its lower convex hull. The hull is nonincreasing and retains every lower bound of $\Xi$. Its forward differences are nonpositive and converge to zero:
--
--   $$
--   \Delta H(m)\le0\quad(m\ge0),\qquad \lim_{m\to\infty}\Delta H(m)=0.
--   $$
--
--   This makes explicit the limiting marginal behavior invoked in the Appendix's existence argument. In combination with positive unit cost, it ensures that the marginal change eventually becomes nonnegative.
-- source:
--   Sherbrooke, METRIC: A Multi-Echelon Technique for Recoverable Item Control, Oper. Res. 16 (1968), p. 140, Appendix, proof of the THEOREM (We use the fact that a monotonically decreasing sequence bounded below has a limit); DOI 10.1287/opre.16.1.122

import Mathlib
import Definitions.Def_SherbrookeMetric_ConvexHull_LowerHull

namespace SherbrookeMetric.ConvexHull

/-- Appendix, proof of the THEOREM, p. 140: the lower hull remains
nonincreasing, has the same lower bounds, and its marginal changes tend to zero. -/
theorem lowerHull_slopes (Ξ : ℕ → ℝ) (hanti : Antitone Ξ)
    (hbdd : BddBelow (Set.range Ξ)) :
    Antitone (lowerHull Ξ) ∧
      (∀ b : ℝ, (∀ k : ℕ, b ≤ Ξ k) → ∀ m : ℕ, b ≤ lowerHull Ξ m) ∧
      (∀ m : ℕ, ServiceParts.StockLevels.fdiff (lowerHull Ξ) m ≤ 0) ∧
      Filter.Tendsto (ServiceParts.StockLevels.fdiff (lowerHull Ξ))
        Filter.atTop (nhds 0) := by sorry

end SherbrookeMetric.ConvexHull
