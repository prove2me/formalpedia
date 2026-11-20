-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_rectangle_root_end_copies
-- name    : QEC.Coding.BDL26RXFaceSecondReadout.rectangle_root_end_copies
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:10:13.259751+00:00
-- url     : https://prove2.me/theorems/79624f92-d5aa-4c86-ab1d-b9ed7414d180
-- title:
--   BDL26 RXFace Second Readout: rectangle root end copies
-- statement:
--   The two opposite actual boundary edges have FORCED DIFFERENT root bits,
--   for every original admissible Cq correction and every possible mixed-edge tie.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L918-L924
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L918-L924

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

theorem QEC.Coding.BDL26RXFaceSecondReadout.rectangle_root_end_copies (z : One.Z)
    (rect : SubdivisionBoundaryEdge (transposePresentation One) z witnessScale) (c : BDL26FiniteTannerSquare.Two) :
    rootWord (BDL26RXFaceEdgeTower.faceOwner witnessScale z (Sum.inr rect))
      (rectangleEndEdge z rect c)=(if c=0 then 0 else 1) := by sorry
