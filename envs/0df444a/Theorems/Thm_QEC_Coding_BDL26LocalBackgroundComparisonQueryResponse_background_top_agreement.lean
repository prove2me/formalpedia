-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonQueryResponse_background_top_agreement
-- name    : QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse.background_top_agreement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T14:36:10.927601+00:00
-- url     : https://prove2.me/theorems/32b3bdec-253c-481b-9d6a-c16cf0bd4bd3
-- title:
--   BDL26 Local Background Comparison Query Response: background top agreement
-- statement:
--   The BDL26 Local Background Comparison Query Response construction uses the background top agreement property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonQueryResponse.lean#L88-L93
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonQueryResponse.lean#L88-L93

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

theorem QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse.background_top_agreement (sigma0 : TopInput S n) (g : W S n)
    (A : Finset (Coordinates S n (TopIndex n))) :
    AgreeOn A (perturbTop S n sigma0 g).val
      (perturbTop S n sigma0 (backgroundRestriction S n g (physicalPullback S n A))).val := by sorry
