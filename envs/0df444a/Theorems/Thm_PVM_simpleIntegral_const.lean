-- Prove2me | Theorems.Thm_PVM_simpleIntegral_const
-- name    : PVM.simpleIntegral_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:54:58.674803+00:00
-- url     : https://prove2.me/theorems/8d451a3a-e7b1-558a-8c4d-9ee5d8139784
-- title:
--   PVM: simple Integral const
-- statement:
--   The spectral sum of a constant simple function is the corresponding scalar operator.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Integral.lean#L458-L465
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Integral.lean#L458-L465

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

theorem PVM.simpleIntegral_const (E_pvm : PVM E) (z : ℂ) :
    E_pvm.simpleIntegral (SimpleFunc.const ℝ z) = z • 1 := by sorry
