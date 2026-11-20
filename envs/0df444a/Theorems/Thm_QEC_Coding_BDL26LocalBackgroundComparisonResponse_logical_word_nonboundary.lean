-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonResponse_logical_word_nonboundary
-- name    : QEC.Coding.BDL26LocalBackgroundComparisonResponse.logical_word_nonboundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T14:21:23.597179+00:00
-- url     : https://prove2.me/theorems/49a690b4-cc80-44ba-aece-5ad0d7013247
-- title:
--   BDL26 Local Background Comparison Response: logical word nonboundary
-- statement:
--   The literal finite-backgroundRestriction generator is a nonboundary in the full top carrier.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonResponse.lean#L83-L88
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonResponse.lean#L83-L88

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

theorem QEC.Coding.BDL26LocalBackgroundComparisonResponse.logical_word_nonboundary (S : OddScale) (n : Nat) (sigma : TopInput S n) :
    logicalError S n ∉ boundaries S n := by sorry
