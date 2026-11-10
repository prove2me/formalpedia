-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocalRootCorrection_coboundary
-- name    : QEC.Coding.BDL26RXLocalReplacement.xLocalRootCorrection_coboundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:29:33.750486+00:00
-- url     : https://prove2.me/theorems/1456402c-f9e2-4377-a307-35e5f2f2ff1b
-- title:
--   BDL26 RXLocal Replacement: x Local Root Correction coboundary
-- statement:
--   The finite connector construction has exactly the four desired root syndromes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L977-L1000
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L977-L1000

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalGridParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeightParity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalConnectingWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_XLocalWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26XLocalGridParity BDL26XLocalWeightParity
open BDL26XLocalConnectingWeight
open scoped BigOperators Classical

theorem QEC.Coding.BDL26RXLocalReplacement.xLocalRootCorrection_coboundary
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (a b l r : Field) (heven : a + b + l + r = 0) :
    wordLinearMapTranspose (doubleCylinderBoundary2 P x S)
        (xLocalRootCorrection P x S face a b l r) =
      Pi.single (xLocalRegionRoot P x S face (Sum.inl 0)) a +
        Pi.single (xLocalRegionRoot P x S face (Sum.inl 1)) b +
        Pi.single (xLocalRegionRoot P x S face (Sum.inr 0)) l +
        Pi.single (xLocalRegionRoot P x S face (Sum.inr 1)) r := by sorry
