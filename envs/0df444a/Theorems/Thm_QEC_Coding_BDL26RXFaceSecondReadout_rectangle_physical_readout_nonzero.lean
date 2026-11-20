-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_rectangle_physical_readout_nonzero
-- name    : QEC.Coding.BDL26RXFaceSecondReadout.rectangle_physical_readout_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:21:19.077036+00:00
-- url     : https://prove2.me/theorems/0325000f-a5b4-4f25-8baf-a294f49dd892
-- title:
--   BDL26 RXFace Second Readout: rectangle physical readout nonzero
-- statement:
--   Nonzero ACTUAL original coarse readout, with the complete physical error
--   and all original Cx/Cq choices retained. The endpoint is constructed internally.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L969-L979
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L969-L979

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

theorem QEC.Coding.BDL26RXFaceSecondReadout.rectangle_physical_readout_nonzero (z : One.Z)
    (rect : SubdivisionBoundaryEdge (transposePresentation One) z witnessScale) :
    physicalReadout witnessScale 1
      (gradientError (BDL26RXFaceEdgeTower.faceOwner witnessScale z (Sum.inr rect))
        (splitPotential (BDL26RXFaceEdgeTower.faceOwner witnessScale z (Sum.inr rect))))≠0 := by sorry
