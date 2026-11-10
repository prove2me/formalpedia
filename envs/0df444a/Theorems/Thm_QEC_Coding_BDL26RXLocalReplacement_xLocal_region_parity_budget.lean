-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_xLocal_region_parity_budget
-- name    : QEC.Coding.BDL26RXLocalReplacement.xLocal_region_parity_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:27:26.973222+00:00
-- url     : https://prove2.me/theorems/013c6d34-f1a7-4d0e-9384-464b1b3173a5
-- title:
--   BDL26 RXLocal Replacement: x Local region parity budget
-- statement:
--   The original four-region parity budget is bounded by the actual syndrome.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L233-L249
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/XLocalWeight.lean#L233-L249

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

theorem QEC.Coding.BDL26RXLocalReplacement.xLocal_region_parity_budget
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (R : TannerSquareCellularRegular P) (x : P.X) (S : OddScale)
    (syndrome : Word Field (DoubleCylinderFace P x S)) :
    (∑ face : XStarFace P x,
      (bitWeight (xLocalRegionParity P x S syndrome face (Sum.inl 0)) +
        bitWeight (xLocalRegionParity P x S syndrome face (Sum.inl 1)) +
        bitWeight (xLocalRegionParity P x S syndrome face (Sum.inr 0)) +
        bitWeight (xLocalRegionParity P x S syndrome face (Sum.inr 1)))) ≤
      HammingWeight syndrome := by sorry
