-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoDecoder_search_head
-- name    : QEC.Coding.BDL26LevelTwoDecoder.search_head
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T10:47:54.556941+00:00
-- url     : https://prove2.me/theorems/8a76e68b-24a2-4242-b531-cf82bdc538e4
-- title:
--   BDL26 Level Two Decoder: search head
-- statement:
--   Search returns a passing head before inspecting its tail.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDecoderZero.lean#L36-L38
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDecoderZero.lean#L36-L38

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoDecoder
open BDL26FiniteTannerSquare BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26TannerLocalRegularity BDL26RZMap1CoordinateBridge
open MultiscaleDecoder

theorem QEC.Coding.BDL26LevelTwoDecoder.search_head {α : Type} (accept : α → Bool) (a : α) (tail : List α)
    (ha : accept a = true) : search accept (a :: tail) = some a := by sorry
