-- Prove2me | Theorems.Thm_PVM_simpleIntegral_piecewise_const
-- name    : PVM.simpleIntegral_piecewise_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:55:42.108072+00:00
-- url     : https://prove2.me/theorems/20bacee6-09ca-4eaf-84b1-7e51d0321001
-- title:
--   PVM: simple Integral piecewise const
-- statement:
--   The spectral sum of `z` on a measurable set and zero off it is `z • E(S)`.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Integral.lean#L486-L523
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Integral.lean#L486-L523

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

theorem PVM.simpleIntegral_piecewise_const (E_pvm : PVM E)
    (S : Set ℝ) (hS : MeasurableSet S) (z : ℂ) :
    E_pvm.simpleIntegral
        (SimpleFunc.piecewise S hS (SimpleFunc.const ℝ z) (SimpleFunc.const ℝ 0)) =
      z • E_pvm.proj S := by sorry
