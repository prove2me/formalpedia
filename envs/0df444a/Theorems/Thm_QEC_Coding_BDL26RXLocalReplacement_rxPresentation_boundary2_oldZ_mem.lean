-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxPresentation_boundary2_oldZ_mem
-- name    : QEC.Coding.BDL26RXLocalReplacement.rxPresentation_boundary2_oldZ_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:42:19.160021+00:00
-- url     : https://prove2.me/theorems/7cdaa4cb-7d3e-4fda-8a8b-050a15d08780
-- title:
--   BDL26 RXLocal Replacement: rx Presentation boundary2 old Z mem
-- statement:
--   Nonzero old-Z restriction supplies an actual original face corner.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPresentationCochain.lean#L546-L580
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPresentationCochain.lean#L546-L580

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RZMap1CoordinateBridge (tannerCoboundary0 tannerCoboundary1)
open scoped BigOperators

theorem QEC.Coding.BDL26RXLocalReplacement.rxPresentation_boundary2_oldZ_mem
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (q : RX1 P S) (z : P.Z × Two)
    (h : rxBoundary2Matrix P S q (Sum.inr z) = 1) :
    rxQZIncidence P S q (Sum.inr z) = true := by sorry
