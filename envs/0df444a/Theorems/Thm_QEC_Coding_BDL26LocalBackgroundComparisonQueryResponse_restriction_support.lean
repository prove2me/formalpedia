-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonQueryResponse_restriction_support
-- name    : QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse.restriction_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T14:36:59.777787+00:00
-- url     : https://prove2.me/theorems/917c84fa-958c-48f8-991f-e03c089ee371
-- title:
--   BDL26 Local Background Comparison Query Response: restriction support
-- statement:
--   The BDL26 Local Background Comparison Query Response construction uses the restriction support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonQueryResponse.lean#L221-L229
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonQueryResponse.lean#L221-L229

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

theorem QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse.restriction_support (sigma0 : TopInput S n) (g e : W S n) :
    hammingSupport (backgroundRestriction S n g (queryMask S n sigma0 g e)) =
      occupiedQueries S n sigma0 g e := by sorry
