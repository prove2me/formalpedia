-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonQueryResponse_pullback_agreement
-- name    : QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse.pullback_agreement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T14:36:23.487233+00:00
-- url     : https://prove2.me/theorems/68690eed-b679-4480-924d-4cd3a65fa1b0
-- title:
--   BDL26 Local Background Comparison Query Response: pullback agreement
-- statement:
--   Literal restriction preserves every requested syndrome coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonQueryResponse.lean#L67-L86
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonQueryResponse.lean#L67-L86

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

theorem QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse.pullback_agreement (g : W S n) (A : Finset (Coordinates S n (TopIndex n))) :
    AgreeOn A ((SuffixData S n).family.coboundary1 (TopIndex n) g)
      ((SuffixData S n).family.coboundary1 (TopIndex n)
        (backgroundRestriction S n g (physicalPullback S n A))) := by sorry
