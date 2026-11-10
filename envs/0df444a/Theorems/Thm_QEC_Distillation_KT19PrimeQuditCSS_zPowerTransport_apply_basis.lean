-- Prove2me | Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_zPowerTransport_apply_basis
-- name    : QEC.Distillation.KT19PrimeQuditCSS.zPowerTransport_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T10:41:46.661054+00:00
-- url     : https://prove2.me/theorems/ff57bd01-5049-44db-8356-66db91dcdfa8
-- title:
--   KT19 Prime Qudit CSS: z Power Transport apply basis
-- statement:
--   A generalized Z power applies its linear phase to a computational ket.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L348-L357
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L348-L357

import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.KT19PrimeQuditCSS
open Semantics
open scoped BigOperators
universe u
attribute [local instance] QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype

theorem QEC.Distillation.KT19PrimeQuditCSS.zPowerTransport_apply_basis (p : Nat) [NeZero p] (slope x : ZMod p) :
    zPowerTransport p slope (quditBasisKet p x) =
      zPowerAmplitude p slope x • quditBasisKet p x := by sorry
