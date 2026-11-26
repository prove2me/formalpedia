-- Prove2me | Theorems.Thm_PalomarCrouzeixPalencia_vonNeumann_inequality
-- name    : PalomarCrouzeixPalencia.vonNeumann_inequality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:50:52.443539+00:00
-- url     : https://prove2.me/theorems/8ce26b57-8c68-4683-bf7b-ded28ae71a38
-- title:
--   Palomar Crouzeix Palencia: von Neumann inequality
-- statement:
--   The Palomar Crouzeix Palencia construction uses the von Neumann inequality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/CrouzeixPalenciaSolution.lean#L70-L74
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/CrouzeixPalenciaSolution.lean#L70-L74

import Definitions.Def_Operator_Dilation_Schaeffer
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
import Definitions.Def_CrouzeixPalenciaSolution
import Theorems.Thm_vonNeumann_inequality

set_option autoImplicit false
open scoped InnerProductSpace Polynomial
open PalomarCrouzeixPalencia
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem PalomarCrouzeixPalencia.vonNeumann_inequality (T : E →L[ℂ] E) (hT : ‖T‖ ≤ 1)
    (p : Polynomial ℂ) :
    ‖Polynomial.aeval T p‖ ≤
      polynomialSupNorm p (Metric.closedBall (0 : ℂ) 1) := by sorry
