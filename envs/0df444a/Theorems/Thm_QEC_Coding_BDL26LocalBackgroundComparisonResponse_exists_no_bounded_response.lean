-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonResponse_exists_no_bounded_response
-- name    : QEC.Coding.BDL26LocalBackgroundComparisonResponse.exists_no_bounded_response
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T14:24:23.534326+00:00
-- url     : https://prove2.me/theorems/45ae2628-872f-4983-bb14-53a338566d77
-- title:
--   BDL26 Local Background Comparison Response: exists no bounded response
-- statement:
--   Quantitative no-go: a constructed bad backgroundRestriction admits no boundary-equivalent
--   restriction of its same background having weight at most B.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonResponse.lean#L138-L156
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonResponse.lean#L138-L156

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NonzeroBackgroundComparisonStability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_StoppedReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonResponse
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalBackgroundComparisonResponse
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26RZMap1CoordinateBridge
open BDL26HistoryLogicalResidual
open scoped Classical BigOperators

theorem QEC.Coding.BDL26LocalBackgroundComparisonResponse.exists_no_bounded_response (S : OddScale) (n B : Nat)
    (large : 28*B+33 ≤ S.ell) (sigma0 : TopInput S n)
    (zero : BDL26AllDepthBottomComparisonStability.baseReadout S n sigma0=0) :
    ∃ (P : Finset (Q S n)) (q : Q S n),
      P ⊆ hammingSupport (logicalError S n) ∧ q ∈ hammingSupport (logicalError S n) ∧ q ∉ P ∧
      let g := backgroundRestriction S n (logicalError S n) P
      BDL26AllDepthBottomComparisonStability.residual S n (perturbTop S n sigma0 g) (canonicalBasisWord (F:=BDL26Field) q) ∉ boundaries S n ∧
      ∀ A : Finset (Q S n), HammingWeight (backgroundRestriction S n g A) ≤ B →
        BDL26AllDepthBottomComparisonStability.residual S n (perturbTop S n sigma0 g) (canonicalBasisWord (F:=BDL26Field) q)-
          BDL26AllDepthBottomComparisonStability.residual S n (perturbTop S n sigma0 (backgroundRestriction S n g A))
            (canonicalBasisWord (F:=BDL26Field) q) ∉ boundaries S n := by sorry
