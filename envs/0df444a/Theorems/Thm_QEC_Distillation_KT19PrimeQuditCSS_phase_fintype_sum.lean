-- Prove2me | Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_phase_fintype_sum
-- name    : QEC.Distillation.KT19PrimeQuditCSS.phase_fintype_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T10:41:57.49107+00:00
-- url     : https://prove2.me/theorems/27cc3c03-e8b1-49b0-8319-7dea293b662d
-- title:
--   KT19 Prime Qudit CSS: phase fintype sum
-- statement:
--   Finite products of the canonical phase are equivalently one phase at the summed exponent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L90-L93
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L90-L93

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

theorem QEC.Distillation.KT19PrimeQuditCSS.phase_fintype_sum (p : Nat) [NeZero p] {Index : Type u} [Fintype Index]
    (f : Index → ZMod p) :
    (∏ index : Index, phase p (f index)) = phase p (∑ index : Index, f index) := by sorry
