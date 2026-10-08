-- Prove2me | Theorems.Thm_SherbrookeMetric_ConvexHull_marginal_unique
-- name    : SherbrookeMetric.ConvexHull.marginal_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:53:05.965015+00:00
-- url     : https://prove2.me/theorems/02caa590-4f1f-4018-b67e-f060f3b1a21f
-- title:
--   Appendix — uniqueness of the solution of (12)
-- statement:
--   Let $\Xi:\mathbb N\to\mathbb R$ be nonincreasing and bounded below, $H$ its lower convex hull, and $c>0$. If stock levels $m$ and $n$ both satisfy the marginal conditions (12), then
--
--   $$m=n.$$
--
--   Thus the rule chooses one stock level for each item. The result concerns uniqueness of the solution of the strict marginal conditions; the original objective can have several minimizers tied in value.
-- source:
--   Sherbrooke, METRIC: A Multi-Echelon Technique for Recoverable Item Control, Oper. Res. 16 (1968), p. 140, Appendix, proof of the THEOREM (Since the function Xi-prime is convex, m-bar_i is unique); DOI 10.1287/opre.16.1.122

import Mathlib
import Definitions.Def_SherbrookeMetric_ConvexHull_LowerHull
import Definitions.Def_SherbrookeMetric_ConvexHull_MarginalConditions

namespace SherbrookeMetric.ConvexHull

/-- Appendix, proof of the THEOREM, p. 140: the solution of (12) is unique,
even though (11) can have other minimizers. -/
theorem marginal_unique (Ξ : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (hanti : Antitone Ξ) (hbdd : BddBelow (Set.range Ξ))
    (m n : ℕ) (hm : MarginalConditions c (lowerHull Ξ) m)
    (hn : MarginalConditions c (lowerHull Ξ) n) : m = n := by sorry

end SherbrookeMetric.ConvexHull
