-- Prove2me | Theorems.Thm_VehicleRoutingSurvey_Routing_compact_matching_cubic_exists
-- name    : VehicleRoutingSurvey.Routing.compact_matching_cubic_exists
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T14:43:43.226056+00:00
-- url     : https://prove2.me/theorems/b0a5e78e-757a-456c-876b-2df124e9c4fc
-- title:
--   Compact minimum-weight perfect matching in cubic arithmetic time
-- statement:
--   There is a fixed arithmetic-RAM block for the compact minimum-weight perfect matching problem used by the rural postman algorithm. The block implements the representation and execution contract `CompactMateBlockSpec` with constant 27648.
-- source:
--   J. K. Lenstra and A. H. G. Rinnooy Kan, Complexity of vehicle routing and scheduling problems (1979), Table 3, printed p. 5. https://ir.cwi.nl/pub/9658/9658D.pdf

import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_Part02

open VehicleRoutingSurvey.Routing

theorem VehicleRoutingSurvey.Routing.compact_matching_cubic_exists : ∃ matching : List ArithmeticInstruction, CompactMateBlockSpec matching 27648 := by sorry
