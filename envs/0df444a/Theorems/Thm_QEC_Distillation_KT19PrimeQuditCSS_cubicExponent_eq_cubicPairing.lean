-- Prove2me | Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_cubicExponent_eq_cubicPairing
-- name    : QEC.Distillation.KT19PrimeQuditCSS.cubicExponent_eq_cubicPairing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T10:41:55.182106+00:00
-- url     : https://prove2.me/theorems/ea891b5c-793e-4d37-a7a7-2bf409438bb3
-- title:
--   KT19 Prime Qudit CSS: cubic Exponent eq cubic Pairing
-- statement:
--   The KT19 Prime Qudit CSS construction uses the cubic Exponent eq cubic Pairing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L598-L604
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L598-L604

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

theorem QEC.Distillation.KT19PrimeQuditCSS.cubicExponent_eq_cubicPairing (p : Nat) [NeZero p] {Site : Type u} [Fintype Site]
    (label : PrimeQuditRegisterLabel p Site) :
    cubicExponent p label = cubicPairing p label label label := by sorry
