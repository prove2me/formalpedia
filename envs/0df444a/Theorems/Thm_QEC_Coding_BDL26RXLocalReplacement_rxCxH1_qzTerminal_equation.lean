-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxCxH1_qzTerminal_equation
-- name    : QEC.Coding.BDL26RXLocalReplacement.rxCxH1_qzTerminal_equation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:22:27.755435+00:00
-- url     : https://prove2.me/theorems/a01bb3f8-56ce-404b-abf6-ef0834b3f8e5
-- title:
--   BDL26 RXLocal Replacement: rx Cx H1 qz Terminal equation
-- statement:
--   Every ordered Q-Z corner has the terminal coboundary equation.  The V2
--   owner selects one corner; cellular face uniqueness identifies that corner,
--   and the final small-square transport supplies the other.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXLocalReplacement.lean#L23521-L23579
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXLocalReplacement.lean#L23521-L23579

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity
universe u

theorem QEC.Coding.BDL26RXLocalReplacement.rxCxH1_qzTerminal_equation
    (P : TannerSquarePresentation) (A3 : TannerSquareAdmissibleV3 P)
    (R : TannerSquareCellularRegular P) (x : P.X) (S : OddScale)
    (word : Word Field (DoubleCylinderEdge P x S))
    (hword : wordLinearMapTranspose (rxCx P x S).boundary2 word = 0)
    (copy : Two) (face : XStarFace P x) (corner : Two)
    (segment : Fin S.half) (hterminal : segment.1 + 1 = S.half) :
    rxCxH1_subdivisionPotential P A3 x S word copy
        (subdivisionSegmentStart P x S
          (xStarFaceQZEdge P x face corner) segment) +
      rxCxH1_subdivisionPotential P A3 x S word copy
        (subdivisionSegmentEnd P x S
          (xStarFaceQZEdge P x face corner) segment) =
      word (Sum.inl (copy, Sum.inl
        (xStarFaceQZEdge P x face corner, segment))) := by sorry
