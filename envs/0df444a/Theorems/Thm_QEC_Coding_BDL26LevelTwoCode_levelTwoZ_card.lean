-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoCode_levelTwoZ_card
-- name    : QEC.Coding.BDL26LevelTwoCode.levelTwoZ_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T04:22:45.795206+00:00
-- url     : https://prove2.me/theorems/049f2123-0f1f-4bab-9438-8b7c4d0cbb2e
-- title:
--   BDL26 Level Two Code: level Two Z card
-- statement:
--   Exact Z-check count from the intrinsic Z-local zero-cell family.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoCode.lean#L187-L192
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoCode.lean#L187-L192

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoCode
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoCode
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26DecodingGraph BDL26QuantitativeBounds
open scoped BigOperators

theorem QEC.Coding.BDL26LevelTwoCode.levelTwoZ_card (S : OddScale) :
    Fintype.card (levelTwoPresentation S).Z =
      ∑ z : (levelOnePresentation S).Z,
        Fintype.card (ZDoubleCylinderVertex (levelOnePresentation S) z S) := by sorry
