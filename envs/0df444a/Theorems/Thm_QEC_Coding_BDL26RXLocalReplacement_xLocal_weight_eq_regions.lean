-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocal_weight_eq_regions
-- name    : QEC.Coding.BDL26RXLocalReplacement.xLocal_weight_eq_regions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:25:31.495198+00:00
-- url     : https://prove2.me/theorems/fe4154ef-aaa3-40f1-a4c8-b70d060cd131
-- title:
--   BDL26 RXLocal Replacement: x Local weight eq regions
-- statement:
--   The local syndrome weight is the sum over the four disjoint face regions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L211-L230
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L211-L230

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

theorem QEC.Coding.BDL26RXLocalReplacement.xLocal_weight_eq_regions
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (x : P.X) (S : OddScale)
    (syndrome : Word Field (DoubleCylinderFace P x S)) :
    HammingWeight syndrome = ∑ face : XStarFace P x,
      (HammingWeight (xLocalLayerWord P x S syndrome face 0) +
        HammingWeight (xLocalLayerWord P x S syndrome face 1) +
        HammingWeight (xLocalStripWord P x S syndrome face 0) +
        HammingWeight (xLocalStripWord P x S syndrome face 1)) := by sorry
