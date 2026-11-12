-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_baseAdapter_decode_zero
-- name    : QEC.Coding.BDL26LevelTwoDecoder.baseAdapter_decode_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T10:49:48.086437+00:00
-- url     : https://prove2.me/theorems/2a3ff758-e635-4c44-a9e8-a2ce8aa9ab3f
-- title:
--   BDL26 Level Two Decoder: base Adapter decode zero
-- statement:
--   The existing F17 adapter stores exactly the same zero-normalized function.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDecoderZero.lean#L95-L96
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDecoderZero.lean#L95-L96

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoDecoder
open BDL26FiniteTannerSquare BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26TannerLocalRegularity BDL26RZMap1CoordinateBridge
open MultiscaleDecoder

theorem QEC.Coding.BDL26LevelTwoDecoder.baseAdapter_decode_zero (S : OddScale) : (baseAdapter S).decode 0 = 0 := by sorry
