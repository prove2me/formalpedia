-- Prove2me | Theorems.Thm_VehicleRoutingSurvey_Routing_H_mCPP_fixed
-- name    : VehicleRoutingSurvey.Routing.H_mCPP_fixed
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T00:11:53.577998+00:00
-- url     : https://prove2.me/theorems/c5a7fc15-d8c6-4f35-8eb7-dadd52cb3cda
-- title:
--   §3 fixed-m exception to Table 2, mCPP
-- statement:
--   Consider the mCPP threshold problem with the service restrictions of Table 1 and the routing objective of §2. For every fixed number m >= 2 of vehicles, both the unrestricted physical-graph language and its planar restriction are binary NP-hard.
--
--   $$\forall m\ge2,\quad \operatorname{NPHard}(L_m)\land\operatorname{NPHard}(L_m^{\mathrm{planar}}).$$
--
--   Fleet tours share a depot, may be idle, and minimize the maximum tour cost. The fleet size is fixed before defining the language.
--
--   Differences from the source:
--   - encoding: finite labeled networks and numerical decision inputs → Fin-indexed vertices and link identities, canonical sign/numerator/denominator rational fields and explicit dimensions; reason: this is a finite input representation, separate from real-weight approximation instances; zero weights, loops and parallel links are retained
--   - encoding: binary NP-hardness for every fixed m >= 2 → NPHard of the separated binary language, quantified outside the language over m; reason: the historical qualification only known is not a claim of failure of strong hardness
--   - encoding: planar physical graph → existence of continuous edge curves with disjoint interiors and injective vertex positions; reason: directions are forgotten only for planarity; loops and parallel links remain distinct
-- source:
--   Report 7919/O, p. 3, §3 fixed-m paragraph and p. 4 Table 2 mCPP; survey [10]. Printed p. 3; PDF 5.

import Definitions.Def_VehicleRoutingSurvey_Routing_Encodings

namespace VehicleRoutingSurvey.Routing

theorem H_mCPP_fixed :
    ∀ m : ℕ, 2 ≤ m →
    ResourceScheduling.Chain.NPHard (binaryLanguage FleetDecision.code (FleetYes .cpp false (some m))) ∧
    ResourceScheduling.Chain.NPHard (binaryLanguage FleetDecision.code (FleetYes .cpp true (some m))) := by sorry

end VehicleRoutingSurvey.Routing
