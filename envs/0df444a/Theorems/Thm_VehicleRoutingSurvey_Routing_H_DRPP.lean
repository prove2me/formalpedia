-- Prove2me | Theorems.Thm_VehicleRoutingSurvey_Routing_H_DRPP
-- name    : VehicleRoutingSurvey.Routing.H_DRPP
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T00:11:57.364494+00:00
-- url     : https://prove2.me/theorems/b971c35c-df39-4f9e-afab-be60c7f36832
-- title:
--   Table 2, DRPP row; §3 planar/unary qualifications
-- statement:
--   Consider the DRPP threshold problem with the service restrictions of Table 1 and the routing objective of §2. Both the unrestricted physical-graph language and its planar restriction are NP-hard in the strong, unary-data sense.
--
--   $$\operatorname{StronglyNPHard}(L)\land\operatorname{StronglyNPHard}(L^{\mathrm{planar}}).$$
--
--   A tour may repeat vertices and links; each traversal contributes its weight.
--
--   Differences from the source:
--   - encoding: finite labeled networks and numerical decision inputs → Fin-indexed vertices and link identities, canonical sign/numerator/denominator rational fields and explicit dimensions; reason: this is a finite input representation, separate from real-weight approximation instances; zero weights, loops and parallel links are retained
--   - encoding: strong NP-hardness with unary data → ResourceScheduling.Chain.StronglyNPHard of the complete numeric code; reason: all counts, endpoints, flags, magnitudes, denominators and decision thresholds are encoded by the published unary encoder; malformed strings are no-instances
--   - encoding: planar physical graph → existence of continuous edge curves with disjoint interiors and injective vertex positions; reason: directions are forgotten only for planarity; loops and parallel links remain distinct
-- source:
--   Lenstra and Rinnooy Kan, Report 7919/O (1979), p. 4, Table 2, DRPP row; p. 3, §3; survey references [21], [12;14;27] for the qualifications. Printed p. 4; PDF 6.

import Definitions.Def_VehicleRoutingSurvey_Routing_Encodings

namespace VehicleRoutingSurvey.Routing

theorem H_DRPP :
    ResourceScheduling.Chain.StronglyNPHard RoutingDecision.code (RoutingYes .drpp false) ∧
    ResourceScheduling.Chain.StronglyNPHard RoutingDecision.code (RoutingYes .drpp true) := by sorry

end VehicleRoutingSurvey.Routing
