-- Prove2me | Theorems.Thm_PVM_simpleIntegral_one
-- name    : PVM.simpleIntegral_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:54:55.449694+00:00
-- url     : https://prove2.me/theorems/845f0a22-5450-53db-b72a-1476f9cf6b45
-- title:
--   PVM: simple Integral one
-- statement:
--   The spectral sum of the unit simple function is the identity operator.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Integral.lean#L478-L483
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Integral.lean#L478-L483

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

theorem PVM.simpleIntegral_one (E_pvm : PVM E) :
    E_pvm.simpleIntegral (1 : SimpleFunc ℝ ℂ) = 1 := by sorry
