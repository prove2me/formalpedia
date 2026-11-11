-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_rawSyndrome_zero
-- name    : QEC.Coding.BDL26LevelTwoDecoder.rawSyndrome_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:16:07.410269+00:00
-- url     : https://prove2.me/theorems/71c9e17f-9bdb-488f-99e2-d6ff4626412b
-- title:
--   BDL26 Level Two Decoder: raw Syndrome zero
-- statement:
--   The literal RZ incidence computation vanishes on zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDecoderZero.lean#L57-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDecoderZero.lean#L57-L59

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoDecoder
open BDL26FiniteTannerSquare BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26TannerLocalRegularity BDL26RZMap1CoordinateBridge
open MultiscaleDecoder

theorem QEC.Coding.BDL26LevelTwoDecoder.rawSyndrome_zero (P : TannerSquarePresentation)
    (hasA : Nonempty (TannerSquareAdmissible P)) (S : OddScale) :
    rawSyndrome P hasA S 0 = 0 := by sorry
