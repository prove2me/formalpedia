-- Prove2me | Theorems.Thm_QEC_Distillation_KT19MagicResource_KT19PrimeQuditCSS_phase_eq_one_iff
-- name    : QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS.phase_eq_one_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T10:49:17.488203+00:00
-- url     : https://prove2.me/theorems/5275efb0-5f50-4c29-bc7a-88495680829b
-- title:
--   KT19 Prime Qudit CSS: phase eq one iff
-- statement:
--   The canonical `ZMod p` character detects the zero label.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/MagicResource.lean#L49-L67
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/MagicResource.lean#L49-L67

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

theorem QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS.phase_eq_one_iff (x : ZMod p) :
    phase p x = 1 ↔ x = 0 := by sorry
