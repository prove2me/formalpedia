-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoCode_levelTwoQ_card_upper
-- name    : QEC.Coding.BDL26LevelTwoCode.levelTwoQ_card_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:46:08.106311+00:00
-- url     : https://prove2.me/theorems/729645e9-531b-4c59-b82a-abb1d2819629
-- title:
--   BDL26 Level Two Code: level Two Q card upper
-- statement:
--   The exact finite recurrence specializes to the level-two stopping code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoCode.lean#L213-L216
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoCode.lean#L213-L216

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoCode
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoCode
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26DecodingGraph BDL26QuantitativeBounds
open scoped BigOperators

theorem QEC.Coding.BDL26LevelTwoCode.levelTwoQ_card_upper (S : OddScale) :
    Fintype.card (levelTwoPresentation S).Q ≤
      8 * (2 * S.ell * (S.ell + 2)) ^ 2 := by sorry
