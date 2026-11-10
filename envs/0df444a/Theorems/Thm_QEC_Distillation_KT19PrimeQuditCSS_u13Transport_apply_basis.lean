-- Prove2me | Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_u13Transport_apply_basis
-- name    : QEC.Distillation.KT19PrimeQuditCSS.u13Transport_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T10:41:50.672271+00:00
-- url     : https://prove2.me/theorems/9077ee8d-ca67-4438-a09b-e87c24c8895c
-- title:
--   KT19 Prime Qudit CSS: u13 Transport apply basis
-- statement:
--   The computational-basis cubic action of `U_{1,3}`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L273-L281
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L273-L281

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

theorem QEC.Distillation.KT19PrimeQuditCSS.u13Transport_apply_basis (p : Nat) [NeZero p] (x : ZMod p) :
    u13Transport p (quditBasisKet p x) =
      u13Amplitude p x • quditBasisKet p x := by sorry
