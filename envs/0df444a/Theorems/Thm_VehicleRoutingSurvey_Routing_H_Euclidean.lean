-- Prove2me | Theorems.Thm_VehicleRoutingSurvey_Routing_H_Euclidean
-- name    : VehicleRoutingSurvey.Routing.H_Euclidean
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T00:12:43.277228+00:00
-- url     : https://prove2.me/theorems/2fa7ef61-725e-476f-a6d3-7e61554b410e
-- title:
--   §3 geometric TSP paragraph
-- statement:
--   Given finitely encoded points in the Euclidean plane and a length threshold, ask whether a cyclic order through all points has total Euclidean length at most that threshold. This geometric traveling salesman decision problem is strongly NP-hard:
--
--   $$\operatorname{StronglyNPHard}(\mathrm{EuclideanTSP}).$$
--
--   The statement uses actual square-root distances and asserts hardness without asserting membership in NP.
--
--   Differences from the source:
--   - encoding: points and Euclidean distances in the plane with unary numerical input → rational coordinate and threshold fields; true real Euclidean square roots; reason: finite numerical coordinates specify the standard decision language; lengths are neither squared nor rounded
--   - encoding: strong NP-hardness with unary data → ResourceScheduling.Chain.StronglyNPHard of the complete numeric code; reason: all counts, endpoints, flags, magnitudes, denominators and decision thresholds are encoded by the published unary encoder; malformed strings are no-instances
-- source:
--   Report 7919/O, p. 3, §3 geometric TSP and unary paragraphs; survey [11;28;12]. Printed p. 3; PDF 5.

import Definitions.Def_VehicleRoutingSurvey_Routing_SchedulingGeometry

namespace VehicleRoutingSurvey.Routing

theorem H_Euclidean :
    ResourceScheduling.Chain.StronglyNPHard EuclideanInstance.code EuclideanYes := by sorry

end VehicleRoutingSurvey.Routing
