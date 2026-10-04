-- Prove2me | Theorems.Thm_ServiceParts_RealTime_Q_convex
-- name    : ServiceParts.RealTime.Q_convex
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T00:01:14.756208+00:00
-- url     : https://prove2.me/theorems/35b4d7ba-13b8-418b-86ec-505d973c1699
-- title:
--   Section 10.2 — the end-of-horizon holding cost Q_ij is convex
-- statement:
--   For every base $j$, the expected end-of-horizon holding cost
--   $$Q_{ij}(S) = h_{ij} \sum_{t = T^r_{ij} + T_{i0} + 1}^{\infty} E[S - X_{ijt}]^+$$
--   is a discretely convex function of the integer stock level $S$: for every integer $S$,
--   $$Q_{ij}(S+1) - Q_{ij}(S) \le Q_{ij}(S+2) - Q_{ij}(S+1).$$
--
--   Convexity of $Q_{ij}$ and of the single-period costs $G_{ijt}$ is what makes the allocation models tractable. The book relies on it for the linear-programming reformulations of Sections 10.4.2 and 10.5.2 and for its greedy algorithms.
--
--   **Formalization Note** The book writes "It is easily shown"; the statement is taken with the standing assumptions of the item model ($h_{ij} > 0$, the series converging at every $S$).
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, p. 234, Section 10.2 (after (10.1))

import Mathlib
import Definitions.Def_ServiceParts_RealTime_Model

open MeasureTheory

namespace ServiceParts.RealTime

/-- Section 10.2, p. 234: the end-of-horizon holding cost `Q_{ij}` (10.1) is a (discretely)
convex function of its argument. -/
theorem Q_convex {J : Type*} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (M : ItemModel J Ω P) (j : J) :
    DiscreteConvex (M.Q j) := by sorry

end ServiceParts.RealTime
