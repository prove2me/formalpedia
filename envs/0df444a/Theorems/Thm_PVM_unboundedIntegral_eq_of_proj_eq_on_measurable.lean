-- Prove2me | Theorems.Thm_PVM_unboundedIntegral_eq_of_proj_eq_on_measurable
-- name    : PVM.unboundedIntegral_eq_of_proj_eq_on_measurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:01:11.133575+00:00
-- url     : https://prove2.me/theorems/610f2bd2-56bf-5c7b-aff1-ad735ebf5d09
-- title:
--   PVM: unbounded Integral eq of proj eq on measurable
-- statement:
--   Unbounded spectral integration depends only on a PVM's values on measurable sets.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Unbounded.lean#L1429-L1444
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Unbounded.lean#L1429-L1444

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
open Filter

theorem PVM.unboundedIntegral_eq_of_proj_eq_on_measurable
    (E₁ E₂ : PVM E)
    (hproj : ∀ S : Set ℝ, MeasurableSet S → E₁.proj S = E₂.proj S)
    (f : ℝ → ℂ) (hf : Measurable f) :
    E₁.unboundedIntegral f hf = E₂.unboundedIntegral f hf := by sorry
