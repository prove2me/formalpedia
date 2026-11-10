-- Prove2me | Theorems.Thm_QEC_Distillation_KT19MagicResource_KT19PrimeQuditCSS_rankOne_adjoint_comp_eq
-- name    : QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS.rankOne_adjoint_comp_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T10:49:08.052439+00:00
-- url     : https://prove2.me/theorems/dcaa9b0b-111e-438f-89cc-9935e1f8b089
-- title:
--   KT19 Prime Qudit CSS: rank One adjoint comp eq
-- statement:
--   For a normalized state the rank-one projector satisfies `χᵗ (χ χᵗ) = χ χᵗ`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/MagicResource.lean#L196-L211
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/MagicResource.lean#L196-L211

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

theorem QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS.rankOne_adjoint_comp_eq {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]
    (χ : H) (hχ : inner ℂ χ χ = 1) :
    (LinearMap.adjoint (InnerProductSpace.rankOne ℂ χ χ).toLinearMap).comp
        (InnerProductSpace.rankOne ℂ χ χ).toLinearMap =
      (InnerProductSpace.rankOne ℂ χ χ).toLinearMap := by sorry
