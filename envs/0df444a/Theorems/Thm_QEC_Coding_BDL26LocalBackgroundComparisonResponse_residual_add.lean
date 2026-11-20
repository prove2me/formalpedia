-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonResponse_residual_add
-- name    : QEC.Coding.BDL26LocalBackgroundComparisonResponse.residual_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T14:26:40.354279+00:00
-- url     : https://prove2.me/theorems/f01303f7-c083-4ffc-bf50-5703177be347
-- title:
--   BDL26 Local Background Comparison Response: residual add
-- statement:
--   Exact telescoping retains both complete correction calls at all three inputs.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonResponse.lean#L54-L66
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonResponse.lean#L54-L66

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NonzeroBackgroundComparisonStability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_StoppedReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonResponse
import Theorems.Thm_QEC_Coding_BDL26GlobalLookupLinearity_residual_add

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalBackgroundComparisonResponse
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26RZMap1CoordinateBridge
open BDL26HistoryLogicalResidual
open scoped Classical BigOperators

theorem QEC.Coding.BDL26LocalBackgroundComparisonResponse.residual_add (S : OddScale) (n : Nat) (sigma : TopInput S n) (a b : W S n) :
    BDL26AllDepthBottomComparisonStability.residual S n sigma (a+b)=
      BDL26AllDepthBottomComparisonStability.residual S n sigma a+BDL26AllDepthBottomComparisonStability.residual S n (perturbTop S n sigma a) b := by sorry
