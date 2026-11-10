-- Prove2me | Theorems.Thm_QEC_Distillation_KT19P11ReedSolomonCubicBridge_p11_physicalU13_implements_inverse
-- name    : QEC.Distillation.KT19P11ReedSolomonCubicBridge.p11_physicalU13_implements_inverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T13:02:00.77604+00:00
-- url     : https://prove2.me/theorems/6f44e5c1-9a8e-4d1d-895f-030790908ad2
-- title:
--   KT19 P11 Reed Solomon Cubic Bridge: p11 physical U13 implements inverse
-- statement:
--   The actual transversal physical `U_{1,3}` implements the constructed
--   inverse logical `U_{1,3}` on the p=11 KT19 cubic CSS code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/P11CubicBridge.lean#L591-L595
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/P11CubicBridge.lean#L591-L595

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

theorem QEC.Distillation.KT19P11ReedSolomonCubicBridge.p11_physicalU13_implements_inverse :
    p11CubicRowFamily.encodedCode.ImplementsLogicalGate
      p11CubicRowFamily.physicalU13 p11CubicRowFamily.logicalInverseU13 := by sorry
