-- Prove2me | Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_u13ConjugatedX_firstDifference_is_pauli
-- name    : QEC.Distillation.KT19PrimeQuditCSS.u13ConjugatedX_firstDifference_is_pauli
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T10:41:35.962114+00:00
-- url     : https://prove2.me/theorems/97758945-72a3-41a8-bc8a-17d4f3fd39be
-- title:
--   KT19 Prime Qudit CSS: u13 Conjugated X first Difference is pauli
-- statement:
--   The next finite difference is, up to a global phase, the actual Pauli Z power.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L385-L390
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/CubicCSS.lean#L385-L390

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

theorem QEC.Distillation.KT19PrimeQuditCSS.u13ConjugatedX_firstDifference_is_pauli (p : Nat) [NeZero p] (x : ZMod p) :
    phase p (u13ConjugatedXExponent p (x + 1) - u13ConjugatedXExponent p x) =
      phase p 6 * zPowerAmplitude p 6 x := by sorry
