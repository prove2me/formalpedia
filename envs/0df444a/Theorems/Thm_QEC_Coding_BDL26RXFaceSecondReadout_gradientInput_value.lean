-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_gradientInput_value
-- name    : QEC.Coding.BDL26RXFaceSecondReadout.gradientInput_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:06:35.758011+00:00
-- url     : https://prove2.me/theorems/5af41f16-79c2-4564-9d34-948d216f89b6
-- title:
--   BDL26 RXFace Second Readout: gradient Input value
-- statement:
--   The actual full syndrome of this local gradient is exactly its outgoing
--   X-to-Q flow. In particular it has neither an X part nor a doubled-Z part.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L600-L617
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L600-L617

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

theorem QEC.Coding.BDL26RXFaceSecondReadout.gradientInput_value (x : P.X) (g : Word F (DoubleCylinderVertex P x witnessScale)) :
    (gradientInput x g).val=xFlow P witnessScale x
      (wordLinearMapTranspose (doubleCylinderBoundary1 P x witnessScale) g) := by sorry
