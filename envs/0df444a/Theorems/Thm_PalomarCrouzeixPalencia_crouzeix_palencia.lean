-- Prove2me | Theorems.Thm_PalomarCrouzeixPalencia_crouzeix_palencia
-- name    : PalomarCrouzeixPalencia.crouzeix_palencia
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:58:05.50683+00:00
-- url     : https://prove2.me/theorems/bb55de1e-38ae-5a87-9834-1230bb38045d
-- title:
--   Palomar Crouzeix Palencia: crouzeix palencia
-- statement:
--   The Palomar Crouzeix Palencia construction uses the crouzeix palencia property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/CrouzeixPalenciaSolution.lean#L76-L79
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/CrouzeixPalenciaSolution.lean#L76-L79

import Definitions.Def_Operator_Dilation_Schaeffer
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
import Definitions.Def_CrouzeixPalenciaSolution
import Theorems.Thm_crouzeix_palencia

set_option autoImplicit false
open scoped InnerProductSpace Polynomial
open PalomarCrouzeixPalencia
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem PalomarCrouzeixPalencia.crouzeix_palencia (A : E →L[ℂ] E) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by sorry
