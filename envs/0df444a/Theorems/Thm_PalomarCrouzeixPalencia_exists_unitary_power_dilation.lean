-- Prove2me | Theorems.Thm_PalomarCrouzeixPalencia_exists_unitary_power_dilation
-- name    : PalomarCrouzeixPalencia.exists_unitary_power_dilation
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:50:45.563851+00:00
-- url     : https://prove2.me/theorems/f09b051e-0433-4212-9de7-fb1d3c6a42b4
-- title:
--   Palomar Crouzeix Palencia: exists unitary power dilation
-- statement:
--   The Palomar Crouzeix Palencia construction uses the exists unitary power dilation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/CrouzeixPalenciaSolution.lean#L61-L68
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/CrouzeixPalenciaSolution.lean#L61-L68

import Definitions.Def_Operator_Dilation_Schaeffer
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
import Definitions.Def_CrouzeixPalenciaSolution
import Theorems.Thm_exists_unitary_power_dilation

set_option autoImplicit false
open scoped InnerProductSpace Polynomial
open PalomarCrouzeixPalencia
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem PalomarCrouzeixPalencia.exists_unitary_power_dilation (T : E →L[ℂ] E) (hT : ‖T‖ ≤ 1) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (V : E →L[ℂ] H) (U : H →L[ℂ] H),
    (∀ x y : E, ⟪V x, V y⟫_ℂ = ⟪x, y⟫_ℂ) ∧
    U ∈ unitary (H →L[ℂ] H) ∧
    (∀ (n : ℕ) (x : E),
      ContinuousLinearMap.adjoint V ((U ^ n) (V x)) = (T ^ n) x) := by sorry
