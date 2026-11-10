-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxPresentation_coboundary0_eq
-- name    : QEC.Coding.BDL26RXLocalReplacement.rxPresentation_coboundary0_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:13:02.602214+00:00
-- url     : https://prove2.me/theorems/92496c33-8fc3-4b26-bd86-e5b4a256f901
-- title:
--   BDL26 RXLocal Replacement: rx Presentation coboundary0 eq
-- statement:
--   The materialized Tanner degree-zero coboundary is the transpose raw boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPresentationCochain.lean#L336-L349
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPresentationCochain.lean#L336-L349

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RZMap1CoordinateBridge (tannerCoboundary0 tannerCoboundary1)
open scoped BigOperators

theorem QEC.Coding.BDL26RXLocalReplacement.rxPresentation_coboundary0_eq
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (_R : TannerSquareCellularRegular P) (S : OddScale) :
    tannerCoboundary0 (rxReplacementPresentation P S) =
      wordLinearMapTranspose (rxBoundary1 P S) := by sorry
