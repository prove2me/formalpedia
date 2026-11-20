-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonQueryResponse_nonboundary_restriction
-- name    : QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse.nonboundary_restriction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T14:37:15.023074+00:00
-- url     : https://prove2.me/theorems/22e514d4-c42d-4c1c-ba95-6d5762d688a5
-- title:
--   BDL26 Local Background Comparison Query Response: nonboundary restriction
-- statement:
--   The BDL26 Local Background Comparison Query Response construction uses the nonboundary restriction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonQueryResponse.lean#L209-L216
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonQueryResponse.lean#L209-L216

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

theorem QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse.nonboundary_restriction (sigma0 : TopInput S n) (g : W S n) (q : Q S n)
    (bad : BDL26AllDepthBottomComparisonStability.residual S n (perturbTop S n sigma0 g)
      (canonicalBasisWord (F:=BDL26Field) q) ∉ boundaries S n) :
    BDL26AllDepthBottomComparisonStability.residual S n
      (perturbTop S n sigma0 (backgroundRestriction S n g
        (queryMask S n sigma0 g (canonicalBasisWord (F:=BDL26Field) q))))
      (canonicalBasisWord (F:=BDL26Field) q) ∉ boundaries S n := by sorry
