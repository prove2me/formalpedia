-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonResponse_exists_bad_prefix
-- name    : QEC.Coding.BDL26LocalBackgroundComparisonResponse.exists_bad_prefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T14:26:51.871249+00:00
-- url     : https://prove2.me/theorems/230c08af-109c-44bb-9963-b9b32a5b6170
-- title:
--   BDL26 Local Background Comparison Response: exists bad prefix
-- statement:
--   A genuine supported-coordinate backgroundRestriction of the actual logical word has a bad
--   next physical flip. No hypothetical terminal residual is supplied.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonResponse.lean#L92-L125
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonResponse.lean#L92-L125

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

theorem QEC.Coding.BDL26LocalBackgroundComparisonResponse.exists_bad_prefix (S : OddScale) (n : Nat) (sigma0 : TopInput S n) :
    ∃ (A : Finset (Q S n)) (q : Q S n),
      A ⊆ hammingSupport (logicalError S n) ∧
      q ∈ hammingSupport (logicalError S n) ∧ q ∉ A ∧
      BDL26AllDepthBottomComparisonStability.residual S n (perturbTop S n sigma0 (backgroundRestriction S n (logicalError S n) A))
        (canonicalBasisWord (F:=BDL26Field) q) ∉ boundaries S n := by sorry
