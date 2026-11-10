-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_rxPresentation_boundary1Matrix_eq
-- name    : QEC.Coding.BDL26RXLocalReplacement.rxPresentation_boundary1Matrix_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:41:44.594263+00:00
-- url     : https://prove2.me/theorems/96635386-44d6-40f3-8ac5-457e8e7fb173
-- title:
--   BDL26 RXLocal Replacement: rx Presentation boundary1 Matrix eq
-- statement:
--   The degree-one raw matrix is the indicator of the actual successor X-Q relation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPresentationCochain.lean#L301-L321
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPresentationCochain.lean#L301-L321

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPresentationCochain
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RZMap1CoordinateBridge (tannerCoboundary0 tannerCoboundary1)
open scoped BigOperators

theorem QEC.Coding.BDL26RXLocalReplacement.rxPresentation_boundary1Matrix_eq
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (x : RX0 P S) (q : RX1 P S) :
    rxBoundary1Matrix P S x q =
      if (rxReplacementPresentation P S).xq x q = true then 1 else 0 := by sorry
