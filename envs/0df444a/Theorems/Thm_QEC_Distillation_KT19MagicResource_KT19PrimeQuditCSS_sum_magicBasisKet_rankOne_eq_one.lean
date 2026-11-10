-- Prove2me | Theorems.Thm_QEC_Distillation_KT19MagicResource_KT19PrimeQuditCSS_sum_magicBasisKet_rankOne_eq_one
-- name    : QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS.sum_magicBasisKet_rankOne_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T10:49:17.620424+00:00
-- url     : https://prove2.me/theorems/65d4c66f-a49c-4aeb-80c4-7b3a9894df57
-- title:
--   KT19 Prime Qudit CSS: sum magic Basis Ket rank One eq one
-- statement:
--   Summing the magic-basis rank-one projectors recovers the identity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/MagicResource.lean#L214-L278
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/MagicResource.lean#L214-L278

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

theorem QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS.sum_magicBasisKet_rankOne_eq_one :
    (∑ a : ZMod p,
        (InnerProductSpace.rankOne ℂ (magicBasisKet p a)
          (magicBasisKet p a)).toLinearMap) = 1 := by sorry
