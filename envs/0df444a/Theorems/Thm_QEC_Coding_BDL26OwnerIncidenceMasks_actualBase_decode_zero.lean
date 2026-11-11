-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OwnerIncidenceMasks_actualBase_decode_zero
-- name    : QEC.Coding.BDL26OwnerIncidenceMasks.actualBase_decode_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:18:17.680355+00:00
-- url     : https://prove2.me/theorems/40150208-c101-432c-adcb-b374274ef60e
-- title:
--   BDL26 Owner Incidence Masks: actual Base decode zero
-- statement:
--   The actual stopped-history base stores the physical-C2 selector unchanged.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDecoderZero.lean#L110-L111
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDecoderZero.lean#L110-L111

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OwnerIncidenceMasks
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RZMap1CoordinateBridge MultiscaleDecoder

theorem QEC.Coding.BDL26OwnerIncidenceMasks.actualBase_decode_zero (S : OddScale) (n : Nat) :
    (actualBase S n).decode 0 = 0 := by sorry
