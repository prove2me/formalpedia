-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonQueryResponse_residual_restriction
-- name    : QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse.residual_restriction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T14:33:05.629252+00:00
-- url     : https://prove2.me/theorems/dc32114c-cfa2-461f-83c0-ffc84798a9e4
-- title:
--   BDL26 Local Background Comparison Query Response: residual restriction
-- statement:
--   Literal full-word replay for every valid seed and physical background.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonQueryResponse.lean#L187-L207
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonQueryResponse.lean#L187-L207

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonDepth
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonQueryResponse
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffix_delta1

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26RZMap1CoordinateBridge
open BDL26HistoryLogicalResidual (suffix_delta1)
open BDL26LocalBackgroundComparisonResponse BDL26PairedHistoryQueryCone
open MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse.residual_restriction (sigma0 : TopInput S n) (g e : W S n) :
    BDL26AllDepthBottomComparisonStability.residual S n (perturbTop S n sigma0 g) e =
      BDL26AllDepthBottomComparisonStability.residual S n
        (perturbTop S n sigma0 (backgroundRestriction S n g (queryMask S n sigma0 g e))) e := by sorry
