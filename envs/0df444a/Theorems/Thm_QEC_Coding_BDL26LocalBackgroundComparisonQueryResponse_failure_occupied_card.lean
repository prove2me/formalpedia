-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonQueryResponse_failure_occupied_card
-- name    : QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse.failure_occupied_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T14:35:33.45182+00:00
-- url     : https://prove2.me/theorems/f1049dfb-122a-41a1-9a00-b9e35fc401ae
-- title:
--   BDL26 Local Background Comparison Query Response: failure occupied card
-- statement:
--   The BDL26 Local Background Comparison Query Response construction uses the failure occupied card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonQueryResponse.lean#L247-L255
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonQueryResponse.lean#L247-L255

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

theorem QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse.failure_occupied_card (B : Nat) (large : 33 ≤ S.ell)
    (deep : 4*B < 2^((n+1)/2)) (g : W S n) (q : Q S n)
    (bad : BDL26AllDepthBottomComparisonStability.residual S n
      (perturbTop S n (BDL26NonzeroBackgroundComparisonStability.zeroInput S n) g)
      (canonicalBasisWord (F:=BDL26Field) q) ∉ boundaries S n) :
    B < (occupiedQueries S n (BDL26NonzeroBackgroundComparisonStability.zeroInput S n)
      g (canonicalBasisWord (F:=BDL26Field) q)).card := by sorry
