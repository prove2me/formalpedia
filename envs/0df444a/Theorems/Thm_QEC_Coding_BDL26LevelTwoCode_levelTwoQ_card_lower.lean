-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoCode_levelTwoQ_card_lower
-- name    : QEC.Coding.BDL26LevelTwoCode.levelTwoQ_card_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T04:22:47.602513+00:00
-- url     : https://prove2.me/theorems/e00d0635-7970-4483-9285-a65688b31586
-- title:
--   BDL26 Level Two Code: level Two Q card lower
-- statement:
--   The actual five-qubit seed and both root injections give a nonzero size.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoCode.lean#L206-L210
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoCode.lean#L206-L210

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoCode
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoCode
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26DecodingGraph BDL26QuantitativeBounds
open scoped BigOperators

theorem QEC.Coding.BDL26LevelTwoCode.levelTwoQ_card_lower (S : OddScale) :
    20 ≤ Fintype.card (levelTwoPresentation S).Q := by sorry
