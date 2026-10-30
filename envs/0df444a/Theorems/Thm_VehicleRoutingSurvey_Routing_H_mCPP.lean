-- Prove2me | Theorems.Thm_VehicleRoutingSurvey_Routing_H_mCPP
-- name    : VehicleRoutingSurvey.Routing.H_mCPP
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T00:11:36.798458+00:00
-- url     : https://prove2.me/theorems/b6e4a74e-a4c8-48d6-a521-6ad8df4a8c1b
-- title:
--   Table 2, mCPP row (m part of input)
-- statement:
--   Consider the mCPP threshold problem with the service restrictions of Table 1 and the routing objective of §2. Both the unrestricted physical-graph language and its planar restriction are NP-hard in the strong, unary-data sense.
--
--   $$\operatorname{StronglyNPHard}(L)\land\operatorname{StronglyNPHard}(L^{\mathrm{planar}}).$$
--
--   Fleet tours share a depot, may be idle, and minimize the maximum tour cost. The positive fleet size is part of the input.
--
--   Differences from the source:
--   - encoding: finite labeled networks and numerical decision inputs → Fin-indexed vertices and link identities, canonical sign/numerator/denominator rational fields and explicit dimensions; reason: this is a finite input representation, separate from real-weight approximation instances; zero weights, loops and parallel links are retained
--   - encoding: strong NP-hardness with unary data → ResourceScheduling.Chain.StronglyNPHard of the complete numeric code; reason: all counts, endpoints, flags, magnitudes, denominators and decision thresholds are encoded by the published unary encoder; malformed strings are no-instances
--   - encoding: planar physical graph → existence of continuous edge curves with disjoint interiors and injective vertex positions; reason: directions are forgotten only for planarity; loops and parallel links remain distinct
-- source:
--   Report 7919/O, p. 4, Table 2, mCPP; p. 3, §3; survey [10;12;14;27]. Printed p. 4; PDF 6.

import Definitions.Def_VehicleRoutingSurvey_Routing_Encodings

namespace VehicleRoutingSurvey.Routing

theorem H_mCPP :
    ResourceScheduling.Chain.StronglyNPHard FleetDecision.code (FleetYes .cpp false none) ∧
    ResourceScheduling.Chain.StronglyNPHard FleetDecision.code (FleetYes .cpp true none) := by sorry

end VehicleRoutingSurvey.Routing
