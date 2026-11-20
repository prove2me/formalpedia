-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_rectangle_closed_end_copies
-- name    : QEC.Coding.BDL26RXFaceSecondReadout.rectangle_closed_end_copies
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:15:37.590538+00:00
-- url     : https://prove2.me/theorems/7e7815b7-5117-4bf0-ad65-6a8a20c4f3b4
-- title:
--   BDL26 RXFace Second Readout: rectangle closed end copies
-- statement:
--   On the literal isolated four-edge rectangle, closedness forces the two
--   end-copy edge coefficients equal. No assertion of this form is made for a
--   general graph; the support assumption contains exactly the actual four slots.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L829-L860
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean#L829-L860

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

theorem QEC.Coding.BDL26RXFaceSecondReadout.rectangle_closed_end_copies (T : TannerSquarePresentation) (x : T.X)
    (S : OddScale) (rect : SubdivisionBoundaryEdge T x S)
    (w : Word F (DoubleCylinderEdge T x S))
    (hs : hammingSupport w⊆Finset.univ.image
      (doubleCylinderRectangleBoundaryEdge T x S rect))
    (hc : doubleCylinderBoundary1 T x S w=0) :
    w (Sum.inl (0,rect.1))=w (Sum.inl (1,rect.1)) := by sorry
