-- Prove2me | Theorems.Thm_PVM_simpleIntegral_zero
-- name    : PVM.simpleIntegral_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:54:53.904075+00:00
-- url     : https://prove2.me/theorems/dfe6d10a-3b99-406d-91c9-439cf9251a15
-- title:
--   PVM: simple Integral zero
-- statement:
--   The spectral sum of the zero simple function is zero.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Integral.lean#L469-L474
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Integral.lean#L469-L474

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

theorem PVM.simpleIntegral_zero (E_pvm : PVM E) :
    E_pvm.simpleIntegral (0 : SimpleFunc ℝ ℂ) = 0 := by sorry
