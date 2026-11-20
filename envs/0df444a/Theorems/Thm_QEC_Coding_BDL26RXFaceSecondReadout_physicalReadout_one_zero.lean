-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_physicalReadout_one_zero
-- name    : QEC.Coding.BDL26RXFaceSecondReadout.physicalReadout_one_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:08:06.142706+00:00
-- url     : https://prove2.me/theorems/b6d29b3d-ecfb-4058-95ff-29edb99f13ff
-- title:
--   BDL26 RXFace Second Readout: physical Readout one zero
-- statement:
--   The empty physical prefix has zero actual FIRST, while its original
--   non-normalized Cx correction is retained.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L386-L388
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L386-L388

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

theorem QEC.Coding.BDL26RXFaceSecondReadout.physicalReadout_one_zero (S : OddScale) : physicalReadout S 1 0=0 := by sorry
