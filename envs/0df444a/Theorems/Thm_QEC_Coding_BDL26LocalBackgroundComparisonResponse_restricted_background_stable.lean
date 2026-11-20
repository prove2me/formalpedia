-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonResponse_restricted_background_stable
-- name    : QEC.Coding.BDL26LocalBackgroundComparisonResponse.restricted_background_stable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T14:24:07.944444+00:00
-- url     : https://prove2.me/theorems/0012163c-6211-4b1c-baba-0a5a7c9406b1
-- title:
--   BDL26 Local Background Comparison Response: restricted background stable
-- statement:
--   Every restricted background within the existing budget has a trivial defect.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonResponse.lean#L128-L134
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonResponse.lean#L128-L134

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

theorem QEC.Coding.BDL26LocalBackgroundComparisonResponse.restricted_background_stable (S : OddScale) (n B : Nat)
    (large : 28*B+33 ≤ S.ell) (sigma0 : TopInput S n)
    (zero : BDL26AllDepthBottomComparisonStability.baseReadout S n sigma0=0) (g : W S n) (A : Finset (Q S n))
    (small : HammingWeight (backgroundRestriction S n g A) ≤ B) (q : Q S n) :
    BDL26AllDepthBottomComparisonStability.residual S n (perturbTop S n sigma0 (backgroundRestriction S n g A))
      (canonicalBasisWord (F:=BDL26Field) q) ∈ boundaries S n := by sorry
