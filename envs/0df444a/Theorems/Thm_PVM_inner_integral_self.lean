-- Prove2me | Theorems.Thm_PVM_inner_integral_self
-- name    : PVM.inner_integral_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:01:20.734689+00:00
-- url     : https://prove2.me/theorems/dc0db50f-9791-4a7f-b416-12dd694f2713
-- title:
--   PVM: inner integral self
-- statement:
--   Diagonal matrix coefficients of bounded measurable spectral integrals are scalar
--   integrals.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Unbounded.lean#L177-L207
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Unbounded.lean#L177-L207

import Definitions.Def_Spectral_PVM_Integral
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Function.L2Space
import Definitions.Def_Spectral_PVM_Unbounded
set_option autoImplicit false
open MeasureTheory
open Function
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem PVM.inner_integral_self (E_pvm : PVM E)
    (f : ℝ → ℂ) (hf : Measurable f) (hbdd : ∃ C, ∀ t, ‖f t‖ ≤ C)
    (x : E) :
    @inner ℂ E _ x (E_pvm.integral f hf hbdd x) =
      ∫ t, f t ∂(E_pvm.scalarMeasure x) := by sorry
