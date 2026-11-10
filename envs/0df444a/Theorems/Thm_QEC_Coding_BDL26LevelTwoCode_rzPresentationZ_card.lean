-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoCode_rzPresentationZ_card
-- name    : QEC.Coding.BDL26LevelTwoCode.rzPresentationZ_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:46:14.322204+00:00
-- url     : https://prove2.me/theorems/c6710b43-02b9-4c3c-9dca-ac219df698ad
-- title:
--   BDL26 Level Two Code: rz Presentation Z card
-- statement:
--   Exact Z-check count from the intrinsic Z-local zero-cell family.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoCode.lean#L134-L144
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoCode.lean#L134-L144

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoCode
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoCode
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26DecodingGraph BDL26QuantitativeBounds
open scoped BigOperators

theorem QEC.Coding.BDL26LevelTwoCode.rzPresentationZ_card (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) :
    Fintype.card (BDL26RZLocalReplacement.rzReplacementPresentation P A S).Z =
      ∑ z : P.Z,
        Fintype.card (ZDoubleCylinderVertex P z S) := by sorry
