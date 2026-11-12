-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoCode_levelTwoFace_card
-- name    : QEC.Coding.BDL26LevelTwoCode.levelTwoFace_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T04:22:44.462186+00:00
-- url     : https://prove2.me/theorems/5f1335d2-1753-4f0b-b9e1-7d0057232fca
-- title:
--   BDL26 Level Two Code: level Two Face card
-- statement:
--   Exact face count, retaining local, Q-Z glue, and old-X-copy faces.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoCode.lean#L195-L204
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoCode.lean#L195-L204

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoCode
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoCode
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26DecodingGraph BDL26QuantitativeBounds
open scoped BigOperators

theorem QEC.Coding.BDL26LevelTwoCode.levelTwoFace_card (S : OddScale) :
    Fintype.card (levelTwoPresentation S).Face =
      (∑ z : (levelOnePresentation S).Z,
        Fintype.card (ZDoubleCylinderFace (levelOnePresentation S) z S) * (2 * 2)) +
      ((∑ e : QZEdge (levelOnePresentation S),
        Fintype.card (QDoubleCylinderEdge
          (transposePresentation (levelOnePresentation S)) e.1.1 S) * 2) +
       Fintype.card (levelOnePresentation S).Face * 2) := by sorry
