-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonResponse_exists_large_bad_prefix
-- name    : QEC.Coding.BDL26LocalBackgroundComparisonResponse.exists_large_bad_prefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T14:24:08.619255+00:00
-- url     : https://prove2.me/theorems/ef24b4f4-4b5a-44b9-9943-591f9dd11a0d
-- title:
--   BDL26 Local Background Comparison Response: exists large bad prefix
-- statement:
--   Fully inhabited actual-family obstruction: zero seed, a nonzero physical
--   background and a nonzero supported single flip, including all positive depths.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonResponse.lean#L183-L204
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonResponse.lean#L183-L204

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

theorem QEC.Coding.BDL26LocalBackgroundComparisonResponse.exists_large_bad_prefix (S : OddScale) (n B : Nat)
    (large : 28*B+33 ≤ S.ell) :
    ∃ (P : Finset (Q S n)) (q : Q S n),
      P ⊆ hammingSupport (logicalError S n) ∧ q ∈ hammingSupport (logicalError S n) ∧ q ∉ P ∧
      let g := backgroundRestriction S n (logicalError S n) P
      B < HammingWeight g ∧ g ≠ 0 ∧
      canonicalBasisWord (F:=BDL26Field) q ≠ (0 : W S n) ∧
      BDL26AllDepthBottomComparisonStability.residual S n
        (perturbTop S n (BDL26NonzeroBackgroundComparisonStability.zeroInput S n) g)
        (canonicalBasisWord (F:=BDL26Field) q) ∉ boundaries S n := by sorry
