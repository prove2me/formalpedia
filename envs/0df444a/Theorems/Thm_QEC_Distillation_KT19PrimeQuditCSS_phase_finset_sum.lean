-- Prove2me | Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_phase_finset_sum
-- name    : QEC.Distillation.KT19PrimeQuditCSS.phase_finset_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T10:41:38.984099+00:00
-- url     : https://prove2.me/theorems/e4469565-073c-4966-95c5-de05c7022054
-- title:
--   KT19 Prime Qudit CSS: phase finset sum
-- statement:
--   The additive character turns every finite sum of field exponents into a product of phases.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L80-L87
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L80-L87

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

theorem QEC.Distillation.KT19PrimeQuditCSS.phase_finset_sum (p : Nat) [NeZero p] {Index : Type u}
    (indices : Finset Index) (f : Index → ZMod p) :
    phase p (∑ index ∈ indices, f index) = ∏ index ∈ indices, phase p (f index) := by sorry
