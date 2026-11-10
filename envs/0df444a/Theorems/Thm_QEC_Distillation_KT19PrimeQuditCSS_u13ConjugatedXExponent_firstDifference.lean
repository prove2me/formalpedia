-- Prove2me | Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_u13ConjugatedXExponent_firstDifference
-- name    : QEC.Distillation.KT19PrimeQuditCSS.u13ConjugatedXExponent_firstDifference
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T10:41:53.38229+00:00
-- url     : https://prove2.me/theorems/f1583f45-83df-4c6e-b4e3-ca0cd345f7c2
-- title:
--   KT19 Prime Qudit CSS: u13 Conjugated XExponent first Difference
-- statement:
--   The finite difference of the conjugated-X quadratic phase is linear.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L366-L369
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L366-L369

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

theorem QEC.Distillation.KT19PrimeQuditCSS.u13ConjugatedXExponent_firstDifference (p : Nat) [NeZero p] (x : ZMod p) :
    u13ConjugatedXExponent p (x + 1) - u13ConjugatedXExponent p x = 6 * x + 6 := by sorry
