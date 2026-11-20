-- Prove2me | Theorems.Thm_QEC_Coding_BDL26AllDepthBottomComparisonStability_baseReadout_original_FIRST
-- name    : QEC.Coding.BDL26AllDepthBottomComparisonStability.baseReadout_original_FIRST
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T14:09:12.918553+00:00
-- url     : https://prove2.me/theorems/7e44b5cb-f0cc-46dc-9294-f0a8496e8313
-- title:
--   BDL26 All Depth Bottom Comparison Stability: base Readout original FIRST
-- statement:
--   The full stored base word equals the existing public FIRST word.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/AllDepthBottomComparisonStability.lean#L295-L298
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/AllDepthBottomComparisonStability.lean#L295-L298

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

theorem QEC.Coding.BDL26AllDepthBottomComparisonStability.baseReadout_original_FIRST (S : OddScale) (n : Nat)
    (u : BDL26TransposedStoppedDecoder.XSyndromeDomain S n) :
    baseReadout S n (BDL26ActualFailureReadout.input S n u)=
      BDL26ActualFailureReadout.firstReadout S n u := by sorry
