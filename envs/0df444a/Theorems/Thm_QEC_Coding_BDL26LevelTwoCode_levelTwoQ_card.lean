-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoCode_levelTwoQ_card
-- name    : QEC.Coding.BDL26LevelTwoCode.levelTwoQ_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T04:23:26.207056+00:00
-- url     : https://prove2.me/theorems/675f3b69-1c61-43c5-a18b-5a68c32176b8
-- title:
--   BDL26 Level Two Code: level Two Q card
-- statement:
--   Exact physical-qubit count from both disjoint RZ degree-one families.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoCode.lean#L177-L184
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoCode.lean#L177-L184

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoCode
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoCode
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26DecodingGraph BDL26QuantitativeBounds
open scoped BigOperators

theorem QEC.Coding.BDL26LevelTwoCode.levelTwoQ_card (S : OddScale) :
    Fintype.card (levelTwoPresentation S).Q =
      (∑ z : (levelOnePresentation S).Z,
        Fintype.card (ZDoubleCylinderEdge (levelOnePresentation S) z S)) +
      (∑ q : (levelOnePresentation S).Q,
        Fintype.card (QDoubleCylinderVertex (transposePresentation (levelOnePresentation S)) q S)) := by sorry
