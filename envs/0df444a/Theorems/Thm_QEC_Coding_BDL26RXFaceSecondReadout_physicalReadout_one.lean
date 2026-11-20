-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_physicalReadout_one
-- name    : QEC.Coding.BDL26RXFaceSecondReadout.physicalReadout_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:12:44.427718+00:00
-- url     : https://prove2.me/theorems/1e39fc77-3a0c-4d14-ab32-d718d1673233
-- title:
--   BDL26 RXFace Second Readout: physical Readout one
-- statement:
--   At n=1 the original fixed-total history makes exactly the actual C3 RX
--   step. This equality uses the original history input and its genuine range proof.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L366-L382
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L366-L382

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

theorem QEC.Coding.BDL26RXFaceSecondReadout.physicalReadout_one (S : OddScale) (e : Word F (Physical S 3)) :
    physicalReadout S 1 e=
      (BDL26RXErrorPullback.run S 3 rxIndex rxIndex_even e).coarse.val := by sorry
