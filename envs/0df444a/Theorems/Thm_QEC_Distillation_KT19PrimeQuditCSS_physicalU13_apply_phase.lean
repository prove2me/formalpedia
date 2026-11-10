-- Prove2me | Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_physicalU13_apply_phase
-- name    : QEC.Distillation.KT19PrimeQuditCSS.physicalU13_apply_phase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T10:42:01.40003+00:00
-- url     : https://prove2.me/theorems/21ce6774-8b7f-4190-a96d-835a4f9c4774
-- title:
--   KT19 Prime Qudit CSS: physical U13 apply phase
-- statement:
--   The physical product acts by the canonical phase of the complete cubic exponent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L544-L551
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L544-L551

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
attribute [local instance] primeQuditRegisterLabelFintype

theorem QEC.Distillation.KT19PrimeQuditCSS.physicalU13_apply_phase (p : Nat) [NeZero p] {Site : Type u}
    [Fintype Site] [DecidableEq Site]
    (psi : PrimeQuditRegister p Site) (label : PrimeQuditRegisterLabel p Site) :
    physicalU13 p psi label = phase p (cubicExponent p label) * psi label := by sorry
