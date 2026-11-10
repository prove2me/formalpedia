-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxPresentation_boundary2Matrix_eq
-- name    : QEC.Coding.BDL26RXLocalReplacement.rxPresentation_boundary2Matrix_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:42:33.392342+00:00
-- url     : https://prove2.me/theorems/9140b673-dd3c-450f-99cf-0f90873ff162
-- title:
--   BDL26 RXLocal Replacement: rx Presentation boundary2 Matrix eq
-- statement:
--   The degree-two raw matrix is the indicator of the actual successor Q-Z relation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPresentationCochain.lean#L583-L610
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPresentationCochain.lean#L583-L610

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RZMap1CoordinateBridge (tannerCoboundary0 tannerCoboundary1)
open scoped BigOperators

theorem QEC.Coding.BDL26RXLocalReplacement.rxPresentation_boundary2Matrix_eq
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (q : RX1 P S) (z : RX2 P S) :
    rxBoundary2Matrix P S q z =
      if (rxReplacementPresentation P S).qz q z = true then 1 else 0 := by sorry
