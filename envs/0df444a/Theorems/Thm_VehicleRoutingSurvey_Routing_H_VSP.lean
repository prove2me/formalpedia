-- Prove2me | Theorems.Thm_VehicleRoutingSurvey_Routing_H_VSP
-- name    : VehicleRoutingSurvey.Routing.H_VSP
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T00:12:51.555095+00:00
-- url     : https://prove2.me/theorems/15685ac5-c7a1-4ed9-85e7-1518cac6140d
-- title:
--   Table 2, VSP (all t_j = 0, all u_j = u)
-- statement:
--   Let the input specify trips with nonnegative trip durations, outbound, return and deadhead travel times, a common completion window [0,u], and a vehicle-count threshold. Each trip must occur once in a depot-returning vehicle route. The resulting threshold decision problem is strongly NP-hard:
--
--   $$\operatorname{StronglyNPHard}(\mathrm{VSP}_{[0,u]}).$$
--
--   This classification retains all travel-time arrays and imposes no metric inequality or additional departure/return horizon.
--
--   Differences from the source:
--   - encoding: finitely many trips and numerical travel/window data → Fin-indexed trips, rational travel durations and window endpoints, and a natural vehicle threshold; reason: all four specified travel arrays and both completion-window bounds are retained in the finite code
--   - encoding: strong NP-hardness with unary data → ResourceScheduling.Chain.StronglyNPHard of the complete numeric code; reason: all counts, endpoints, flags, magnitudes, denominators and decision thresholds are encoded by the published unary encoder; malformed strings are no-instances
--   - reading: trips completed within intervals → windows constrain completion times, with explicit departure and return variables; reason: an interval containing the entire trip would make the fixed-time scheduling row infeasible for positive trip duration
-- source:
--   Report 7919/O, p. 4, Table 2 VSP common-window row; p. 3 strong-hardness paragraph; survey [22] (Unpublished), [12]. Printed p. 4; PDF 6.

import Definitions.Def_VehicleRoutingSurvey_Routing_SchedulingGeometry

namespace VehicleRoutingSurvey.Routing

theorem H_VSP :
    ResourceScheduling.Chain.StronglyNPHard VehicleScheduleInstance.code ScheduleYes := by sorry

end VehicleRoutingSurvey.Routing
