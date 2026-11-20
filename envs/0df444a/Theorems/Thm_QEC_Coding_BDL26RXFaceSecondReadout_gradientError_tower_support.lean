-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_gradientError_tower_support
-- name    : QEC.Coding.BDL26RXFaceSecondReadout.gradientError_tower_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:10:33.917712+00:00
-- url     : https://prove2.me/theorems/070302bd-7663-4558-b914-495245b302e5
-- title:
--   BDL26 RXFace Second Readout: gradient Error tower support
-- statement:
--   Every physical flip in the full local-gradient word is a literal seed of
--   this face's original tower. No arbitrary owner is substituted for the face.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L788-L813
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L788-L813

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

theorem QEC.Coding.BDL26RXFaceSecondReadout.gradientError_tower_support (z : (RawOne witnessScale).Z)
    (f : ZDoubleCylinderFace (RawOne witnessScale) z witnessScale)
    (g : Word F (DoubleCylinderVertex P
      (BDL26RXFaceEdgeTower.faceOwner witnessScale z f) witnessScale))
    (q : Physical witnessScale 3)
    (hq : q∈hammingSupport
      (gradientError (BDL26RXFaceEdgeTower.faceOwner witnessScale z f) g)) :
    Nonempty (BDL26RXFaceEdgeTower.Tower witnessScale 1 q) := by sorry
