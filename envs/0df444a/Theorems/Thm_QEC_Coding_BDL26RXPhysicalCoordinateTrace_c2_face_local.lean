-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPhysicalCoordinateTrace_c2_face_local
-- name    : QEC.Coding.BDL26RXPhysicalCoordinateTrace.c2_face_local
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:21:54.509005+00:00
-- url     : https://prove2.me/theorems/4e3e1446-3c02-44be-b173-b2e47903d96b
-- title:
--   BDL26 RXPhysical Coordinate Trace: c2 face local
-- statement:
--   The BDL26 RXPhysical Coordinate Trace construction uses the c2 face local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPhysicalCoordinateTrace/Semantics.lean#L187-L208
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPhysicalCoordinateTrace/Semantics.lean#L187-L208

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPhysicalCoordinateTrace
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LocalSearchFailureReduction
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPhysicalCoordinateTrace_Semantics
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXPhysicalCoordinateTrace
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26CSSHamiltonian BDL26ActualFailureReadout
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RZMap1CoordinateBridge
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26OwnerIncidenceMasks
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXPhysicalCoordinateTrace.c2_face_local (S : OddScale) (N : Nat) (u : XSyndromeDomain S N)
    (q : Physical S (N+2)) (a : BDL26RXFaceEdgeTower.Seed S)
    (hh : hammingSupport (descent S N u q).word ⊆
      BDL26RXPhysicalStarTransport.physicalXStar (state S 2).presentation
        (BDL26RXFaceEdgeTower.faceOwner S a.1 a.2.1)) :
    levelTwoLocalError S (descent S N u q).word := by sorry
