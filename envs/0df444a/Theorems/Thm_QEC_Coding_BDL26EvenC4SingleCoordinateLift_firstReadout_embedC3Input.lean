-- Prove2me | Theorems.Thm_QEC_Coding_BDL26EvenC4SingleCoordinateLift_firstReadout_embedC3Input
-- name    : QEC.Coding.BDL26EvenC4SingleCoordinateLift.firstReadout_embedC3Input
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:46:09.230114+00:00
-- url     : https://prove2.me/theorems/a4ebecd0-c1c9-48fc-ad86-9f67da6015c5
-- title:
--   BDL26 Even C4 Single Coordinate Lift: first Readout embed C3 Input
-- statement:
--   The BDL26 Even C4 Single Coordinate Lift construction uses the first Readout embed C3 Input property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/EvenC4SingleCoordinateLift.lean#L391-L393
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/EvenC4SingleCoordinateLift.lean#L391-L393

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_ActualFailureReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_EvenC4SingleCoordinateLift
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26EvenC4SingleCoordinateLift
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26AlternatingCochain BDL26OwnerIncidenceMasks
open BDL26TransposedStoppedDecoder BDL26CSSHamiltonian
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26HistoryLogicalResidual BDL26ActualFailureReadout
open BDL26RZMap1CoordinateBridge
open RXCoarseGraining RXCoarseGrainingData
open scoped Classical

theorem QEC.Coding.BDL26EvenC4SingleCoordinateLift.firstReadout_embedC3Input (S : OddScale) (u : XSyndromeDomain S 1) :
    firstReadout S 2 (embedC3Input S u)=firstReadout S 1 u := by sorry
