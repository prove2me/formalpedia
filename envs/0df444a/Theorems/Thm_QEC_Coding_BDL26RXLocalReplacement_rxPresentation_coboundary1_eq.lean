-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxPresentation_coboundary1_eq
-- name    : QEC.Coding.BDL26RXLocalReplacement.rxPresentation_coboundary1_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:09:21.401792+00:00
-- url     : https://prove2.me/theorems/2ea3ad8e-aaa5-48c2-977a-57814afbd494
-- title:
--   BDL26 RXLocal Replacement: rx Presentation coboundary1 eq
-- statement:
--   The materialized Tanner degree-one coboundary is the transpose raw boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPresentationCochain.lean#L625-L638
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPresentationCochain.lean#L625-L638

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RZMap1CoordinateBridge (tannerCoboundary0 tannerCoboundary1)
open scoped BigOperators

theorem QEC.Coding.BDL26RXLocalReplacement.rxPresentation_coboundary1_eq
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (_R : TannerSquareCellularRegular P) (S : OddScale) :
    tannerCoboundary1 (rxReplacementPresentation P S) =
      wordLinearMapTranspose (rxBoundary2 P S) := by sorry
