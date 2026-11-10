-- Prove2me | Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_idealU13Resource_inner_self
-- name    : QEC.Distillation.KT19PrimeQuditCSS.idealU13Resource_inner_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T10:43:20.222642+00:00
-- url     : https://prove2.me/theorems/bf175a3b-4391-4d3a-a608-90c97bed8447
-- title:
--   KT19 Prime Qudit CSS: ideal U13 Resource inner self
-- statement:
--   The p-dependent ideal cubic resource is a normalized physical state.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L294-L311
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L294-L311

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

theorem QEC.Distillation.KT19PrimeQuditCSS.idealU13Resource_inner_self (p : Nat) [NeZero p] :
    inner Complex (idealU13Resource p) (idealU13Resource p) = 1 := by sorry
