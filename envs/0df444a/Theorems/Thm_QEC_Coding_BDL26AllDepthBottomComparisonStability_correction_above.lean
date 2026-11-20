-- Prove2me | Theorems.Thm_QEC_Coding_BDL26AllDepthBottomComparisonStability_correction_above
-- name    : QEC.Coding.BDL26AllDepthBottomComparisonStability.correction_above
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T14:11:40.143499+00:00
-- url     : https://prove2.me/theorems/00fcdf36-901c-4eb5-bcb3-8343ebf67633
-- title:
--   BDL26 All Depth Bottom Comparison Stability: correction above
-- statement:
--   Exact operational meaning: same above-C2 sums and one new bottom call.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/AllDepthBottomComparisonStability.lean#L81-L95
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/AllDepthBottomComparisonStability.lean#L81-L95

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

theorem QEC.Coding.BDL26AllDepthBottomComparisonStability.correction_above (S : OddScale) (n : Nat) (sigma : TopInput S n) :
    correction S n sigma = correctionIntervalSum S n sigma 0 (TopIndex n) +
      intervalMap1 (Data S n) 0 (TopIndex n) (Nat.zero_le _)
        (baseComparison S n sigma) := by sorry
