-- Prove2me | Theorems.Thm_QEC_Distillation_KT19P11ReedSolomonCubicBridge_p11_stabilizerCarrier_eq_shortenedReedSolomon
-- name    : QEC.Distillation.KT19P11ReedSolomonCubicBridge.p11_stabilizerCarrier_eq_shortenedReedSolomon
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T13:02:03.136208+00:00
-- url     : https://prove2.me/theorems/6f158049-4fb4-47f1-9f6e-38ddbbf1b66e
-- title:
--   KT19 P11 Reed Solomon Cubic Bridge: p11 stabilizer Carrier eq shortened Reed Solomon
-- statement:
--   The literal stabilizer-row span is the actual shortened `RS_4` code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/P11CubicBridge.lean#L315-L320
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/P11CubicBridge.lean#L315-L320

import Definitions.Def_QEC_Coding_ReedSolomon_Punctured
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_P11CubicBridge
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.KT19P11ReedSolomonCubicBridge
open QEC.Coding
open QEC.Coding.KT19ReedSolomon
open QEC.Distillation.KT19PrimeQuditCSS
open scoped BigOperators
attribute [local instance] QEC.Distillation.KT19P11ReedSolomonCubicBridge.p11Prime
attribute [local instance] QEC.Distillation.KT19P11ReedSolomonCubicBridge.p11NeZero
attribute [local instance] QEC.Distillation.KT19P11ReedSolomonCubicBridge.p11PrimeQuditRegisterLabelFintype
attribute [local instance] p11Prime p11NeZero p11PrimeQuditRegisterLabelFintype

theorem QEC.Distillation.KT19P11ReedSolomonCubicBridge.p11_stabilizerCarrier_eq_shortenedReedSolomon :
    p11StabilizerCarrier = (shortenedReedSolomonCode 11 4 2).carrier := by sorry
