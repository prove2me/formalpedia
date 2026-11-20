-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonQueryResponse_queryMask_window_card
-- name    : QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse.queryMask_window_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T14:36:34.433388+00:00
-- url     : https://prove2.me/theorems/6a2d40f3-9abe-4e6d-966d-99711d555afd
-- title:
--   BDL26 Local Background Comparison Query Response: query Mask window card
-- statement:
--   The BDL26 Local Background Comparison Query Response construction uses the query Mask window card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonQueryResponse.lean#L272-L278
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonQueryResponse.lean#L272-L278

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

theorem QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse.queryMask_window_card (sigma0 : TopInput S n) (g e : W S n)
    (L w : Nat) (hstop : 0 < (queryStop S n sigma0 g e).val)
    (hlen : n-(queryStop S n sigma0 g e).val ≤ L)
    (hw : HammingWeight ((SuffixData S n).family.coboundary1 (TopIndex n) e) ≤ w) :
    (queryMask S n sigma0 g e).card ≤ 7*windowBudget S L w := by sorry
