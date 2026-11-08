-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_rzXQH0ToH1_coordinate
-- name    : QEC.Coding.BDL26RZLocalReplacement.rzXQH0ToH1_coordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:58:17.193103+00:00
-- url     : https://prove2.me/theorems/0f0a565e-9b8c-4003-876c-a08cdddcc12a
-- title:
--   BDL26 RZLocal Replacement: rz XQH0 To H1 coordinate
-- statement:
--   F09 X-Q quotient-coordinate formula: the induced map is the codiagonal
--   in the named F07 charts.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZLocalReplacement.lean#L16912-L16931
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZLocalReplacement.lean#L16912-L16931

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26RZLocalReplacement
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity

theorem QEC.Coding.BDL26RZLocalReplacement.rzXQH0ToH1_coordinate (P : TannerSquarePresentation)
    (q : P.Q) (x : P.X) (hxq : P.xq x q = true) (S : OddScale)
    (cohomologyClass : RZXH0 P x) :
    rzCqH1Coordinate P q S
        (rzXQH0ToH1 P q x hxq S cohomologyClass) =
      (rzCxH0Coordinates P x cohomologyClass).1 +
        (rzCxH0Coordinates P x cohomologyClass).2 := by sorry
