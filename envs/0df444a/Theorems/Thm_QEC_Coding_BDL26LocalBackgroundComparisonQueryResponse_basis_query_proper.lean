-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonQueryResponse_basis_query_proper
-- name    : QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse.basis_query_proper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T14:36:35.238961+00:00
-- url     : https://prove2.me/theorems/2280251b-2c7e-416a-a818-3a15334fba0d
-- title:
--   BDL26 Local Background Comparison Query Response: basis query proper
-- statement:
--   The BDL26 Local Background Comparison Query Response construction uses the basis query proper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonQueryResponse.lean#L365-L374
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonQueryResponse.lean#L365-L374

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

theorem QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse.basis_query_proper (hn : 7 ≤ n) (odd : n % 2 = 1)
    (large : fiveStepPhysicalBudget S < 5*2^(n+2)) (q : Q S n) :
    queryMask S n (BDL26NonzeroBackgroundComparisonStability.zeroInput S n)
      (canonicalBasisWord (F:=BDL26Field) q) (canonicalBasisWord (F:=BDL26Field) q) ≠ Finset.univ := by sorry
