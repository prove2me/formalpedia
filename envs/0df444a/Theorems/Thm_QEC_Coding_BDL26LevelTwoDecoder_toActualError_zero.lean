-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_toActualError_zero
-- name    : QEC.Coding.BDL26LevelTwoDecoder.toActualError_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:13:02.172213+00:00
-- url     : https://prove2.me/theorems/9ee6ee54-2624-4d2d-b7f6-9f7c6d776d78
-- title:
--   BDL26 Level Two Decoder: to Actual Error zero
-- statement:
--   The BDL26 Level Two Decoder construction uses the to Actual Error zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDecoderZero.lean#L87-L87
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDecoderZero.lean#L87-L87

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoDecoder
open BDL26FiniteTannerSquare BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26TannerLocalRegularity BDL26RZMap1CoordinateBridge
open MultiscaleDecoder

theorem QEC.Coding.BDL26LevelTwoDecoder.toActualError_zero (S : OddScale) : toActualError S 0 = 0 := by sorry
