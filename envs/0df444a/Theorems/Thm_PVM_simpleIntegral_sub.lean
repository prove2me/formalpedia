-- Prove2me | Theorems.Thm_PVM_simpleIntegral_sub
-- name    : PVM.simpleIntegral_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:55:01.896665+00:00
-- url     : https://prove2.me/theorems/c4aa38e1-1639-41b6-8d2a-97d21a8de28a
-- title:
--   PVM: simple Integral sub
-- statement:
--   Simple spectral integration preserves subtraction.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Integral.lean#L109-L112
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Integral.lean#L109-L112

import Definitions.Def_Spectral_PVM_Basic
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Topology.UniformSpace.Dini
import Definitions.Def_Spectral_PVM_Integral
set_option autoImplicit false
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem PVM.simpleIntegral_sub (E_pvm : PVM E) (f g : SimpleFunc ℝ ℂ) :
    E_pvm.simpleIntegral (f - g) = E_pvm.simpleIntegral f - E_pvm.simpleIntegral g := by sorry
