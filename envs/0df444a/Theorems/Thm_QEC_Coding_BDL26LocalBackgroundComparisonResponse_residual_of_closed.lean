-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonResponse_residual_of_closed
-- name    : QEC.Coding.BDL26LocalBackgroundComparisonResponse.residual_of_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T14:22:04.442167+00:00
-- url     : https://prove2.me/theorems/77332c87-dd11-45c6-9004-93721bd1a848
-- title:
--   BDL26 Local Background Comparison Response: residual of closed
-- statement:
--   A closed full word returns to exactly the same input, without a selector law.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonResponse.lean#L73-L80
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonResponse.lean#L73-L80

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NonzeroBackgroundComparisonStability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_StoppedReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonResponse
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalBackgroundComparisonResponse
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26RZMap1CoordinateBridge
open BDL26HistoryLogicalResidual
open scoped Classical BigOperators

theorem QEC.Coding.BDL26LocalBackgroundComparisonResponse.residual_of_closed (S : OddScale) (n : Nat) (sigma : TopInput S n)
    (w : W S n) (closed : (SuffixData S n).family.coboundary1 (TopIndex n) w=0) :
    BDL26AllDepthBottomComparisonStability.residual S n sigma w=w := by sorry
