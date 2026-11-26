-- Prove2me | Theorems.Thm_PVM_scalarMeasure_proj
-- name    : PVM.scalarMeasure_proj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:01:50.859947+00:00
-- url     : https://prove2.me/theorems/906fcda2-8231-485c-a8e1-ec8372f3bf9e
-- title:
--   PVM: scalar Measure proj
-- statement:
--   Projecting a vector restricts its scalar measure to the projection set.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Unbounded.lean#L316-L323
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Unbounded.lean#L316-L323

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

theorem PVM.scalarMeasure_proj (E_pvm : PVM E) (x : E) (S : Set ℝ)
    (hS : MeasurableSet S) :
    E_pvm.scalarMeasure (E_pvm.proj S x) = (E_pvm.scalarMeasure x).restrict S := by sorry
