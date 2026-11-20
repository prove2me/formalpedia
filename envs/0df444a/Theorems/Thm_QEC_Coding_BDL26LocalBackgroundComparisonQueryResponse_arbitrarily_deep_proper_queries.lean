-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonQueryResponse_arbitrarily_deep_proper_queries
-- name    : QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse.arbitrarily_deep_proper_queries
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T14:39:59.679244+00:00
-- url     : https://prove2.me/theorems/4e246c73-9e52-4a59-b8f1-14dfe10e4a02
-- title:
--   BDL26 Local Background Comparison Query Response: arbitrarily deep proper queries
-- statement:
--   At every scale, arbitrarily deep actual nonzero basis pairs have a proper
--   physical footprint whose budget depends only on the five-step window and S.
--   This is an existence theorem about the constructed queryMask, not a supplied
--   coalescence or properness certificate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonQueryResponse.lean#L401-L423
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonQueryResponse.lean#L401-L423

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

theorem QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse.arbitrarily_deep_proper_queries (lowerDepth : Nat) :
    ∃ n : Nat, lowerDepth ≤ n ∧ 7 ≤ n ∧ n % 2 = 1 ∧
      ∃ q : Q S n,
        let zero := BDL26NonzeroBackgroundComparisonStability.zeroInput S n
        let e : W S n := canonicalBasisWord (F:=BDL26Field) q
        e ≠ 0 ∧ (SuffixData S n).family.coboundary1 (TopIndex n) e ≠ 0 ∧
        0 < (queryStop S n zero e e).val ∧
        n-(queryStop S n zero e e).val ≤ 5 ∧
        (queryMask S n zero e e).card ≤ fiveStepPhysicalBudget S ∧
        queryMask S n zero e e ≠ Finset.univ ∧
        BDL26AllDepthBottomComparisonStability.residual S n (perturbTop S n zero e) e =
          BDL26AllDepthBottomComparisonStability.residual S n
            (perturbTop S n zero (backgroundRestriction S n e (queryMask S n zero e e))) e := by sorry
