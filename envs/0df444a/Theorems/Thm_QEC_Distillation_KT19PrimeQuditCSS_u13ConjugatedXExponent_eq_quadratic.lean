-- Prove2me | Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_u13ConjugatedXExponent_eq_quadratic
-- name    : QEC.Distillation.KT19PrimeQuditCSS.u13ConjugatedXExponent_eq_quadratic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T10:41:48.080419+00:00
-- url     : https://prove2.me/theorems/74d6e355-ce0e-4f60-9abc-de8cc40caf80
-- title:
--   KT19 Prime Qudit CSS: u13 Conjugated XExponent eq quadratic
-- statement:
--   The cubic finite difference is visibly a quadratic polynomial.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L360-L363
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L360-L363

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

theorem QEC.Distillation.KT19PrimeQuditCSS.u13ConjugatedXExponent_eq_quadratic (p : Nat) [NeZero p] (x : ZMod p) :
    u13ConjugatedXExponent p x = 3 * x ^ 2 + 3 * x + 1 := by sorry
