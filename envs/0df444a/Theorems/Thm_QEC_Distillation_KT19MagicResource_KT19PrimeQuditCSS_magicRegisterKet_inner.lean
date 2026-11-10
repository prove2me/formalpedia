-- Prove2me | Theorems.Thm_QEC_Distillation_KT19MagicResource_KT19PrimeQuditCSS_magicRegisterKet_inner
-- name    : QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS.magicRegisterKet_inner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T10:50:12.336199+00:00
-- url     : https://prove2.me/theorems/598b050c-139d-4bfd-94ca-8a8a862e90f6
-- title:
--   KT19 Prime Qudit CSS: magic Register Ket inner
-- statement:
--   The magic-register kets are an orthonormal basis, obtained by applying
--   the physical cubic unitary to the character basis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/MagicResource.lean#L732-L741
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/MagicResource.lean#L732-L741

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

theorem QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS.magicRegisterKet_inner (e f : PrimeQuditRegisterLabel p Site) :
    inner ℂ (magicRegisterKet p e) (magicRegisterKet p f) =
      if e = f then 1 else 0 := by sorry
