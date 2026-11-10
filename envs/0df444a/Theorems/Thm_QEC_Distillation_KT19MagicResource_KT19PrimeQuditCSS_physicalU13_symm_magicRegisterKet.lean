-- Prove2me | Theorems.Thm_QEC_Distillation_KT19MagicResource_KT19PrimeQuditCSS_physicalU13_symm_magicRegisterKet
-- name    : QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS.physicalU13_symm_magicRegisterKet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T10:49:14.41444+00:00
-- url     : https://prove2.me/theorems/f82c4879-aa99-4bb9-9dce-4f59b2993755
-- title:
--   KT19 Prime Qudit CSS: physical U13 symm magic Register Ket
-- statement:
--   The inverse physical cubic transports the magic register ket to its character ket.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/MagicResource.lean#L708-L715
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/MagicResource.lean#L708-L715

import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_MagicResource
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm

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

theorem QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS.physicalU13_symm_magicRegisterKet (e : PrimeQuditRegisterLabel p Site) :
    (physicalU13 p).symm (magicRegisterKet p e) = characterKet p e := by sorry
