-- Prove2me | Theorems.Thm_SherbrookeMetric_ConvexHull_appendix_theorem
-- name    : SherbrookeMetric.ConvexHull.appendix_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:53:30.257526+00:00
-- url     : https://prove2.me/theorems/30844497-ae79-4ec7-a2ab-fe31a1dd2317
-- title:
--   Appendix THEOREM — the unique marginal allocation minimizes the original cost
-- statement:
--   Consider finitely many items $i$. For each item, let $c_i>0$ be its unit cost and let $\Xi_i:\mathbb N\to\mathbb R$ be a nonincreasing function with a finite lower bound. Write $H_i$ for the greatest discretely convex minorant of $\Xi_i$. Then each item has exactly one stock level $\bar m_i$ satisfying the marginal conditions (12). Every vector $\bar m$ of such levels minimizes the original separable objective over all vectors of nonnegative integer stock levels:
--
--   $$
--   \sum_i\bigl(c_i\bar m_i+\Xi_i(\bar m_i)\bigr)
--   \le\sum_i\bigl(c_i m_i+\Xi_i(m_i)\bigr)
--   \qquad\text{for every }m\in\mathbb N^I.
--   $$
--
--   This justifies Sherbrooke's marginal allocation rule after convexifying possibly nonconvex item backorder functions. Equations (7)–(9) motivate the rule in the METRIC model; the Appendix result itself uses only the abstract item functions stated here.
--
--   **Formalization Note** The paper's “nonnegative and not all zero” costs are corrected to $c_i>0$ for every present item. For $c=0$ and $\Xi(m)=1/(m+1)$, (12) has no solution. “Unique optimizing” is read as uniqueness of the solution selected by (12), not uniqueness of every minimizer of (11): with $c=1$ and $\Xi(0)=1$, $\Xi(m)=0$ for $m\ge1$, the levels $0$ and $1$ tie. At $\bar m=0$ the second line of (12) follows the paper's $H(-1)=+\infty$ convention.
-- source:
--   Sherbrooke, METRIC: A Multi-Echelon Technique for Recoverable Item Control, Oper. Res. 16 (1968), p. 140, Appendix THEOREM, Eqs. (11)–(12), with proof ending p. 141; DOI 10.1287/opre.16.1.122

import Mathlib
import Definitions.Def_SherbrookeMetric_ConvexHull_LowerHull
import Definitions.Def_SherbrookeMetric_ConvexHull_MarginalConditions
import Definitions.Def_SherbrookeMetric_ConvexHull_Objective

namespace SherbrookeMetric.ConvexHull

/-- Appendix THEOREM, p. 140, with the unit-cost correction recorded in the
mission notes: the marginal conditions select one vector, and that vector
minimizes equation (11) with the original item functions. -/
theorem appendix_theorem {ι : Type*} [Fintype ι] (c : ι → ℝ) (Ξ : ι → ℕ → ℝ)
    (hc : ∀ i : ι, 0 < c i) (hanti : ∀ i : ι, Antitone (Ξ i))
    (hbdd : ∀ i : ι, BddBelow (Set.range (Ξ i))) :
    (∀ i : ι, ∃! m : ℕ, MarginalConditions (c i) (lowerHull (Ξ i)) m) ∧
      ∀ mbar : ι → ℕ,
        (∀ i : ι, MarginalConditions (c i) (lowerHull (Ξ i)) (mbar i)) →
          ∀ m : ι → ℕ, objective c Ξ mbar ≤ objective c Ξ m := by sorry

end SherbrookeMetric.ConvexHull
