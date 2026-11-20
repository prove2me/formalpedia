-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonQueryResponse_basis_query_five_window
-- name    : QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse.basis_query_five_window
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T14:37:01.766176+00:00
-- url     : https://prove2.me/theorems/eccfee1b-5f36-4665-aa0d-7eec8204d5b8
-- title:
--   BDL26 Local Background Comparison Query Response: basis query five window
-- statement:
--   The BDL26 Local Background Comparison Query Response construction uses the basis query five window property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonQueryResponse.lean#L350-L363
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonQueryResponse.lean#L350-L363

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

theorem QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse.basis_query_five_window (hn : 7 ≤ n) (odd : n % 2 = 1) (q : Q S n) :
    let zero := BDL26NonzeroBackgroundComparisonStability.zeroInput S n
    let e : W S n := canonicalBasisWord (F:=BDL26Field) q
    0 < (queryStop S n zero e e).val ∧
      n-(queryStop S n zero e e).val ≤ 5 ∧
      (queryMask S n zero e e).card ≤ fiveStepPhysicalBudget S := by sorry
