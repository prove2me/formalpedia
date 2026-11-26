-- Prove2me | Theorems.Thm_PVM_scalarContent_proj
-- name    : PVM.scalarContent_proj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:01:06.578463+00:00
-- url     : https://prove2.me/theorems/a63f31cf-2bd2-589d-9c1b-609fba9b4744
-- title:
--   PVM: scalar Content proj
-- statement:
--   Projecting the vector restricts its scalar content to the projection set.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Unbounded.lean#L307-L313
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Unbounded.lean#L307-L313

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

theorem PVM.scalarContent_proj (E_pvm : PVM E) (x : E) (S T : Set ℝ)
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    E_pvm.scalarContent (E_pvm.proj S x) T = E_pvm.scalarContent x (T ∩ S) := by sorry
