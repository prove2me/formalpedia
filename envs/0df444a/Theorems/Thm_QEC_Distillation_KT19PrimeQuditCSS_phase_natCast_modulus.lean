-- Prove2me | Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_phase_natCast_modulus
-- name    : QEC.Distillation.KT19PrimeQuditCSS.phase_natCast_modulus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T10:42:56.345335+00:00
-- url     : https://prove2.me/theorems/4fe4fbc0-f6f9-4eb1-b0fc-569bdd012bb0
-- title:
--   KT19 Prime Qudit CSS: phase nat Cast modulus
-- statement:
--   The actual root of unity has order dividing its nonzero modulus.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L71-L72
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L71-L72

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

theorem QEC.Distillation.KT19PrimeQuditCSS.phase_natCast_modulus (p : Nat) [NeZero p] : phase p (p : ZMod p) = 1 := by sorry
