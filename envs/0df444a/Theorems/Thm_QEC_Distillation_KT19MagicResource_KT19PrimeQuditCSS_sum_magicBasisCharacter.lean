-- Prove2me | Theorems.Thm_QEC_Distillation_KT19MagicResource_KT19PrimeQuditCSS_sum_magicBasisCharacter
-- name    : QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS.sum_magicBasisCharacter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T10:49:25.981651+00:00
-- url     : https://prove2.me/theorems/e3a176b6-f155-436c-a056-6582394a5843
-- title:
--   KT19 Prime Qudit CSS: sum magic Basis Character
-- statement:
--   The magic-basis amplitudes separate labels through the character sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/MagicResource.lean#L174-L193
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/MagicResource.lean#L174-L193

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

theorem QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS.sum_magicBasisCharacter (y x : ZMod p) :
    (∑ a : ZMod p, starRingEnd ℂ (magicBasisAmplitude p a y) * magicBasisAmplitude p a x) =
      if y = x then (p : ℂ) else 0 := by sorry
