-- Prove2me | Theorems.Thm_QEC_Coding_BDL26AllDepthBottomComparisonStability_source_even_single_flip_stable
-- name    : QEC.Coding.BDL26AllDepthBottomComparisonStability.source_even_single_flip_stable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T14:12:36.424663+00:00
-- url     : https://prove2.me/theorems/0d09b7d8-954a-41e9-b570-cc07d0bf384a
-- title:
--   BDL26 All Depth Bottom Comparison Stability: source even single flip stable
-- statement:
--   The exact source-even physical depths include k=1, the empty suffix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/AllDepthBottomComparisonStability.lean#L288-L292
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/AllDepthBottomComparisonStability.lean#L288-L292

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

theorem QEC.Coding.BDL26AllDepthBottomComparisonStability.source_even_single_flip_stable (S : OddScale) (k : Nat) (hk : 1≤k)
    (large : 16 ≤ S.half) (sigma : TopInput S (2*(k-1)))
    (zero : baseReadout S (2*(k-1)) sigma=0) :
    2*(k-1)+2=2*k ∧ SingleFlipStable S (2*(k-1)) sigma := by sorry
