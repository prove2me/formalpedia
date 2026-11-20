-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalSearchFailureReduction_mem_firstEvent
-- name    : QEC.Coding.BDL26LocalSearchFailureReduction.mem_firstEvent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:10:47.397546+00:00
-- url     : https://prove2.me/theorems/4c9fe39b-67b9-413c-971a-c951203124c1
-- title:
--   BDL26 Local Search Failure Reduction: mem first Event
-- statement:
--   The BDL26 Local Search Failure Reduction construction uses the mem first Event property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LocalSearchFailureReduction.lean#L322-L324
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/LocalSearchFailureReduction.lean#L322-L324

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

theorem QEC.Coding.BDL26LocalSearchFailureReduction.mem_firstEvent (S : OddScale) (n : Nat) (u : XSyndromeDomain S n) :
    u ∈ firstEvent S n ↔ firstReadout S n u≠0 := by sorry
