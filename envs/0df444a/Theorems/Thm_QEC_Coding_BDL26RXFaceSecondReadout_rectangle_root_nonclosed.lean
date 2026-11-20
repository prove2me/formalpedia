-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_rectangle_root_nonclosed
-- name    : QEC.Coding.BDL26RXFaceSecondReadout.rectangle_root_nonclosed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:10:19.674555+00:00
-- url     : https://prove2.me/theorems/71569544-1dd6-4b23-b07c-70dc3a76737b
-- title:
--   BDL26 RXFace Second Readout: rectangle root nonclosed
-- statement:
--   Exact four-slot support and actual RZ local cycle equations rule out a
--   closed root word: its two end-copy coefficients were forced to be 0 and 1.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L929-L965
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L929-L965

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

theorem QEC.Coding.BDL26RXFaceSecondReadout.rectangle_root_nonclosed (z : One.Z)
    (rect : SubdivisionBoundaryEdge (transposePresentation One) z witnessScale) :
    tannerCoboundary1 P
      (rootWord (BDL26RXFaceEdgeTower.faceOwner witnessScale z (Sum.inr rect)))≠0 := by sorry
