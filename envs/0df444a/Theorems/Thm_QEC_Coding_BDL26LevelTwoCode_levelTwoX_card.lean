-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoCode_levelTwoX_card
-- name    : QEC.Coding.BDL26LevelTwoCode.levelTwoX_card
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T04:22:10.733892+00:00
-- url     : https://prove2.me/theorems/f253692f-6ce7-4b40-b781-46b3ef63e7ab
-- title:
--   BDL26 Level Two Code: level Two X card
-- statement:
--   Exact X-check count: Z-local faces, Q-local edges, and two copies of old X.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoCode.lean#L166-L174
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoCode.lean#L166-L174

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoCode
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoCode
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26DecodingGraph BDL26QuantitativeBounds
open scoped BigOperators

theorem QEC.Coding.BDL26LevelTwoCode.levelTwoX_card (S : OddScale) :
    Fintype.card (levelTwoPresentation S).X =
      ((∑ z : (levelOnePresentation S).Z,
        Fintype.card (ZDoubleCylinderFace (levelOnePresentation S) z S)) +
       (∑ q : (levelOnePresentation S).Q,
        Fintype.card (QDoubleCylinderEdge (transposePresentation (levelOnePresentation S)) q S))) +
      Fintype.card (levelOnePresentation S).X * 2 := by sorry
