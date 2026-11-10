-- Prove2me | Theorems.Thm_QEC_Distillation_KT19MagicResource_KT19PrimeQuditCSS_sum_register_phase
-- name    : QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS.sum_register_phase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T10:49:12.593316+00:00
-- url     : https://prove2.me/theorems/b94bdc40-6bea-421b-bb9f-99ad0e678b0b
-- title:
--   KT19 Prime Qudit CSS: sum register phase
-- statement:
--   Summing the character over all register labels separates the zero word.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/MagicResource.lean#L521-L546
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/MagicResource.lean#L521-L546

import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_MagicResource
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.KT19MagicResource
open Semantics
open QEC.Distillation.KT19PrimeQuditCSS
open scoped BigOperators
open QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS
universe u v w
variable (p : Nat) [NeZero p]
variable {Site : Type u} [Fintype Site]
attribute [local instance] QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS._p2m_local_instance_d135975d44_41
attribute [local instance] QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS.primeQuditRegisterLabelFintypeLocal

theorem QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS.sum_register_phase (f : PrimeQuditRegisterLabel p Site) :
    ∑ x : PrimeQuditRegisterLabel p Site, phase p (registerPairing p f x) =
      if f = 0 then (p : ℂ) ^ Fintype.card Site else 0 := by sorry
