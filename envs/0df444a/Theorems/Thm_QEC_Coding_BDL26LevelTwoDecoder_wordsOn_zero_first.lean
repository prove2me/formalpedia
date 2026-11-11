-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_wordsOn_zero_first
-- name    : QEC.Coding.BDL26LevelTwoDecoder.wordsOn_zero_first
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:15:24.603446+00:00
-- url     : https://prove2.me/theorems/e21fc149-b83e-4735-a462-41e39586e85f
-- title:
--   BDL26 Level Two Decoder: words On zero first
-- statement:
--   Binary enumeration starts with zero even when the list repeats coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDecoderZero.lean#L17-L28
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDecoderZero.lean#L17-L28

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoDecoder
open BDL26FiniteTannerSquare BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26TannerLocalRegularity BDL26RZMap1CoordinateBridge
open MultiscaleDecoder

theorem QEC.Coding.BDL26LevelTwoDecoder.wordsOn_zero_first {α : Type} [DecidableEq α] (qs : List α) :
    ∃ tail, wordsOn qs = (0 : Word (ZMod 2) α) :: tail := by sorry
