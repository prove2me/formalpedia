-- Prove2me | Theorems.Thm_ServiceParts_RealTime_G_convex
-- name    : ServiceParts.RealTime.G_convex
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T00:07:22.125573+00:00
-- url     : https://prove2.me/theorems/868ae311-ef77-45c6-bbe4-6f7e91abe7c6
-- title:
--   Section 10.4.2 — the single-period cost G_ijt is convex
-- statement:
--   For every base $j$ and period $t$, the single-period expected holding and backorder cost
--   $$G_{ijt}(S) = h_{ij}\, E[S - X_{ijt}]^+ + b_{ij}\, E[X_{ijt} - S]^+$$
--   is a discretely convex function of the integer stock level $S$: for every integer $S$,
--   $$G_{ijt}(S+1) - G_{ijt}(S) \le G_{ijt}(S+2) - G_{ijt}(S+1).$$
--
--   The book uses this property to solve the constrained newsvendor problem $\mathrm{CN}_{ijt}$ and in the exchange arguments of Theorems 15 and 16.
--
--   **Formalization Note** The cumulative demand $X_{ijt}$ has finite mean (a field of the item model), so both expectations are finite.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, p. 237, Section 10.4.2 (before (10.18))

import Mathlib
import Definitions.Def_ServiceParts_RealTime_Model

open MeasureTheory

namespace ServiceParts.RealTime

/-- Section 10.4.2, p. 237: the single-period cost `G_{ijt}` is a (discretely) convex function
of its argument. -/
theorem G_convex {J : Type*} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (M : ItemModel J Ω P) (j : J) (t : ℕ) :
    DiscreteConvex (M.G j t) := by sorry

end ServiceParts.RealTime
