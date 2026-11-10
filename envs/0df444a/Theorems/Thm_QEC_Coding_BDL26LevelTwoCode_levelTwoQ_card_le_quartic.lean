-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoCode_levelTwoQ_card_le_quartic
-- name    : QEC.Coding.BDL26LevelTwoCode.levelTwoQ_card_le_quartic
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T04:23:20.35424+00:00
-- url     : https://prove2.me/theorems/ff68e85c-6a10-4d35-b904-b8bd4d74ef45
-- title:
--   BDL26 Level Two Code: level Two Q card le quartic
-- statement:
--   A uniform explicit witness for the source O(ell^4) claim.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoCode.lean#L219-L230
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoCode.lean#L219-L230

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoCode
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoCode
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26DecodingGraph BDL26QuantitativeBounds
open scoped BigOperators

theorem QEC.Coding.BDL26LevelTwoCode.levelTwoQ_card_le_quartic (S : OddScale) :
    Fintype.card (levelTwoPresentation S).Q ≤ 288 * S.ell ^ 4 := by sorry
