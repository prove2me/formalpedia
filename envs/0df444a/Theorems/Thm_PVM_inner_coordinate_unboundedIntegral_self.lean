-- Prove2me | Theorems.Thm_PVM_inner_coordinate_unboundedIntegral_self
-- name    : PVM.inner_coordinate_unboundedIntegral_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:01:09.051024+00:00
-- url     : https://prove2.me/theorems/e453f0de-a918-548b-97a4-8b37a89b8b27
-- title:
--   PVM: inner coordinate unbounded Integral self
-- statement:
--   The diagonal matrix coefficient of the coordinate spectral integral is
--   the first moment of the associated scalar spectral measure.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Unbounded.lean#L651-L710
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Unbounded.lean#L651-L710

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

theorem PVM.inner_coordinate_unboundedIntegral_self (E_pvm : PVM E)
    (x : (E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
      Complex.continuous_ofReal.measurable).domain) :
    @inner ℂ E _ (x : E)
        (E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
          Complex.continuous_ofReal.measurable x) =
      ∫ t, (t : ℂ) ∂(E_pvm.scalarMeasure (x : E)) := by sorry
