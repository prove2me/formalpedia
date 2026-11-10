-- Prove2me | Theorems.Thm_QEC_Distillation_KT19P11ReedSolomonCubicBridge_p11_rowCarrier_eq_dual_shortenedComplement
-- name    : QEC.Distillation.KT19P11ReedSolomonCubicBridge.p11_rowCarrier_eq_dual_shortenedComplement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T13:02:29.12154+00:00
-- url     : https://prove2.me/theorems/950b4323-fdc0-480c-9eca-3d7cc9fc7803
-- title:
--   KT19 P11 Reed Solomon Cubic Bridge: p11 row Carrier eq dual shortened Complement
-- statement:
--   The displayed row carrier is the exact complementary shortened-code dual.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/P11CubicBridge.lean#L331-L335
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/P11CubicBridge.lean#L331-L335

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

theorem QEC.Distillation.KT19P11ReedSolomonCubicBridge.p11_rowCarrier_eq_dual_shortenedComplement :
    p11RowCarrier = (shortenedReedSolomonCode 11 7 2).dual.carrier := by sorry
