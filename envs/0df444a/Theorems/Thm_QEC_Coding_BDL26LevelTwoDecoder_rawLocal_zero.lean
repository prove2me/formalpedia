-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_rawLocal_zero
-- name    : QEC.Coding.BDL26LevelTwoDecoder.rawLocal_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:16:08.304886+00:00
-- url     : https://prove2.me/theorems/bb4eb72e-dc7d-4a4e-80a6-3e5301d3422d
-- title:
--   BDL26 Level Two Decoder: raw Local zero
-- statement:
--   An actual owner witnesses the vacuous zero-support locality condition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDecoderZero.lean#L62-L65
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDecoderZero.lean#L62-L65

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoDecoder
open BDL26FiniteTannerSquare BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26TannerLocalRegularity BDL26RZMap1CoordinateBridge
open MultiscaleDecoder

theorem QEC.Coding.BDL26LevelTwoDecoder.rawLocal_zero (P : TannerSquarePresentation) (S : OddScale)
    (center : Vertex P) : rawLocal P S 0 = true := by sorry
