-- Prove2me | Theorems.Thm_VehicleRoutingSurvey_Routing_N_unary
-- name    : VehicleRoutingSurvey.Routing.N_unary
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T00:12:49.005729+00:00
-- url     : https://prove2.me/theorems/3bbfeb22-bfdb-47af-99ff-1bedb4d32d7a
-- title:
--   Table 4, any unary NP-hard problem, algorithm polynomial in problem size and 1/ε for all ε > 0
-- statement:
--   Let P be any encoded real-valued minimization problem whose threshold decision language is NP-hard when all numerical input data are unary. If P admits one uniform fully polynomial approximation scheme, then
--
--   $$\mathrm{P}=\mathrm{NP}.$$
--
--   The printed universal wording is retained without an integrality or objective-gap assumption. INSIGHTS.yaml records the rational-objective counterexample finding separately; it does not change this target.
--
--   Differences from the source:
--   - reading: any unary NP-hard problem → all encoded real-valued minimization problems, without an objective-gap restriction; reason: retains the literal universal wording, including its rational-valued counterexample
--   - encoding: polynomial in problem size and inverse positive tolerance → a single Cook transducer with unary k+1 for tolerance 1/(k+1); reason: rounding up inverse tolerance gives every positive tolerance with only polynomial overhead
--   - encoding: strong NP-hardness with unary data → ResourceScheduling.Chain.StronglyNPHard of the complete numeric code; reason: all counts, endpoints, flags, magnitudes, denominators and decision thresholds are encoded by the published unary encoder; malformed strings are no-instances
-- source:
--   Report 7919/O, p. 6, Table 4, any unary NP-hard problem / algorithm polynomial in problem size and 1/ε for all ε > 0; §4 model comments; survey [12]. Printed p. 6; PDF 8.

import Definitions.Def_VehicleRoutingSurvey_Routing_Approximation

namespace VehicleRoutingSurvey.Routing

theorem N_unary :
    ∀ P : MinimizationProblem,
    ResourceScheduling.Chain.StronglyNPHard thresholdCode (ThresholdYes P) →
    HasFPTAS P → ClassesEqual := by sorry

end VehicleRoutingSurvey.Routing
