-- Prove2me | Theorems.Thm_QEC_Coding_BDL26AllDepthBottomComparisonStability_original_input_single_flip_stable
-- name    : QEC.Coding.BDL26AllDepthBottomComparisonStability.original_input_single_flip_stable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T14:13:16.309281+00:00
-- url     : https://prove2.me/theorems/2fae5ffa-94ac-4fd1-a6a0-1d4c9774bdc0
-- title:
--   BDL26 All Depth Bottom Comparison Stability: original input single flip stable
-- statement:
--   Actual physical-input consumer of the existing complete FIRST word.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/AllDepthBottomComparisonStability.lean#L312-L317
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/AllDepthBottomComparisonStability.lean#L312-L317

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_ActualFailureReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_EvenC4OldXEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AllDepthBottomComparisonStability
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26AllDepthBottomComparisonStability
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26HistoryLogicalResidual BDL26RZMap1CoordinateBridge
open scoped Classical BigOperators

theorem QEC.Coding.BDL26AllDepthBottomComparisonStability.original_input_single_flip_stable (S : OddScale) (n : Nat) (large : 16≤S.half)
    (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n)
    (zero : BDL26ActualFailureReadout.firstReadout S n u=0) :
    SingleFlipStable S n (BDL26ActualFailureReadout.input S n u) := by sorry
