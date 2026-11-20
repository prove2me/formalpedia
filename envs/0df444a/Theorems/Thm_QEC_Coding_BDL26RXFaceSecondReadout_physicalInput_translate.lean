-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_physicalInput_translate
-- name    : QEC.Coding.BDL26RXFaceSecondReadout.physicalInput_translate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:06:17.746956+00:00
-- url     : https://prove2.me/theorems/df7b071e-a5d0-40af-aea0-94cbe2910648
-- title:
--   BDL26 RXFace Second Readout: physical Input translate
-- statement:
--   The BDL26 RXFace Second Readout construction uses the physical Input translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L150-L154
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L150-L154

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceEdgeTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceSecondReadout
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXFaceSecondReadout
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian BDL26ActualFailureReadout BDL26RXDecoderAdapter
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXFaceSecondReadout.physicalInput_translate (S : OddScale) (n : Nat)
    (a b : Word F (Physical S (n+2))) :
    translateX S n (physicalInput S n a) b=physicalInput S n (a+b) := by sorry
