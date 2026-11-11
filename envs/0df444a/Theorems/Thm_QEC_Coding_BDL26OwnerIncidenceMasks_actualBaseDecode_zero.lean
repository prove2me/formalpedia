-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OwnerIncidenceMasks_actualBaseDecode_zero
-- name    : QEC.Coding.BDL26OwnerIncidenceMasks.actualBaseDecode_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:17:51.093071+00:00
-- url     : https://prove2.me/theorems/937c351b-4dd5-4b8b-a4d0-f73613431722
-- title:
--   BDL26 Owner Incidence Masks: actual Base Decode zero
-- statement:
--   Suffix index zero is physical C2, at every total depth n+2.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDecoderZero.lean#L106-L107
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDecoderZero.lean#L106-L107

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OwnerIncidenceMasks
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RZMap1CoordinateBridge MultiscaleDecoder

theorem QEC.Coding.BDL26OwnerIncidenceMasks.actualBaseDecode_zero (S : OddScale) (n : Nat) : actualBaseDecode S n 0 = 0 := by sorry
