-- Prove2me | Theorems.Thm_SherbrookeMetric_ConvexHull_marginal_exists
-- name    : SherbrookeMetric.ConvexHull.marginal_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:53:03.130976+00:00
-- url     : https://prove2.me/theorems/f35c11c3-423b-417f-b5ad-f018041e6c3d
-- title:
--   Appendix — existence of a solution of (12)
-- statement:
--   Let $\Xi:\mathbb N\to\mathbb R$ be nonincreasing and bounded below, $H$ its lower convex hull, and $c>0$ the unit cost. Then there is a stock level satisfying both marginal conditions (12):
--
--   $$
--   \exists\bar m\in\mathbb N:\quad c+H(\bar m+1)-H(\bar m)\ge0,
--   \quad \bar m>0\Longrightarrow c+H(\bar m)-H(\bar m-1)<0.
--   $$
--
--   This is the existence half of the rule that selects the allocation stock level.
--
--   **Formalization Note** The paper says “nonnegative” cost, but its claim fails at $c=0$: $\Xi(m)=1/(m+1)$ is already convex and has no stock level meeting the first inequality. The theorem therefore uses strictly positive cost.
-- source:
--   Sherbrooke, METRIC: A Multi-Echelon Technique for Recoverable Item Control, Oper. Res. 16 (1968), p. 140, Appendix, proof of the THEOREM (This shows that equation (12) has at least one solution); DOI 10.1287/opre.16.1.122

import Mathlib
import Definitions.Def_SherbrookeMetric_ConvexHull_LowerHull
import Definitions.Def_SherbrookeMetric_ConvexHull_MarginalConditions

namespace SherbrookeMetric.ConvexHull

/-- Appendix, proof of the THEOREM, p. 140: corrected to strictly positive
unit cost, which the stated nonnegative version requires for existence. -/
theorem marginal_exists (Ξ : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (hanti : Antitone Ξ) (hbdd : BddBelow (Set.range Ξ)) :
    ∃ m : ℕ, MarginalConditions c (lowerHull Ξ) m := by sorry

end SherbrookeMetric.ConvexHull
