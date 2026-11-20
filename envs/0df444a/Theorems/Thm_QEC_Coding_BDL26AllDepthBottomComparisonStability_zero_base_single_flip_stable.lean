-- Prove2me | Theorems.Thm_QEC_Coding_BDL26AllDepthBottomComparisonStability_zero_base_single_flip_stable
-- name    : QEC.Coding.BDL26AllDepthBottomComparisonStability.zero_base_single_flip_stable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T14:12:26.442148+00:00
-- url     : https://prove2.me/theorems/b026d6a3-253a-4c91-ab38-909843a1dee5
-- title:
--   BDL26 All Depth Bottom Comparison Stability: zero base single flip stable
-- statement:
--   The BDL26 All Depth Bottom Comparison Stability construction uses the zero base single flip stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/AllDepthBottomComparisonStability.lean#L279-L285
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/AllDepthBottomComparisonStability.lean#L279-L285

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

theorem QEC.Coding.BDL26AllDepthBottomComparisonStability.zero_base_single_flip_stable (S : OddScale) (n : Nat) (large : 16 ≤ S.half)
    (sigma : TopInput S n) (zero : baseReadout S n sigma=0) :
    SingleFlipStable S n sigma := by sorry
