-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocalRootCorrection_weight_le
-- name    : QEC.Coding.BDL26RXLocalReplacement.xLocalRootCorrection_weight_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:29:08.952236+00:00
-- url     : https://prove2.me/theorems/d2997024-bd56-481f-9fd2-4cc6eacfa081
-- title:
--   BDL26 RXLocal Replacement: x Local Root Correction weight le
-- statement:
--   The connector construction obeys the exact four-region crossing budget.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L1003-L1033
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L1003-L1033

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

theorem QEC.Coding.BDL26RXLocalReplacement.xLocalRootCorrection_weight_le
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (R : TannerSquareCellularRegular P) (x : P.X) (S : OddScale)
    (face : XStarFace P x) (a b l r : Field) (heven : a + b + l + r = 0) :
    connectingWeight P A x S (xLocalRootCorrection P x S face a b l r) ≤
      pieceCrossingCost a b l r := by sorry
