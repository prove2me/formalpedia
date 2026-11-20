-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalSearchFailureReduction_badX_subset_events
-- name    : QEC.Coding.BDL26LocalSearchFailureReduction.badX_subset_events
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:08:01.883713+00:00
-- url     : https://prove2.me/theorems/fa673c99-e865-4788-8c99-304d32abc3b3
-- title:
--   BDL26 Local Search Failure Reduction: bad X subset events
-- statement:
--   A second unresolved event is kept; this is NOT badX bounded by FIRST alone.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LocalSearchFailureReduction.lean#L332-L345
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LocalSearchFailureReduction.lean#L332-L345

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroFaceEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LocalSearchFailureReduction
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalSearchFailureReduction
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian BDL26ActualFailureReadout
open scoped Classical BigOperators

theorem QEC.Coding.BDL26LocalSearchFailureReduction.badX_subset_events (S : OddScale) (n : Nat) :
    BDL26LogicalDefectProtection.badX S n ⊆ firstEvent S n ∪ searchFailureEvent S n := by sorry
