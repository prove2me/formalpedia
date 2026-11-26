-- Prove2me | Theorems.Thm_PVM_ofReal_norm_sq_integral_sub_unboundedIntegral
-- name    : PVM.ofReal_norm_sq_integral_sub_unboundedIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:01:05.362828+00:00
-- url     : https://prove2.me/theorems/7a6984d7-3dbd-5b8c-89db-148d5140d9c7
-- title:
--   PVM: of Real norm sq integral sub unbounded Integral
-- statement:
--   The pointwise `L²` identity comparing a bounded spectral integral with an unbounded
--   spectral integral on the latter's domain.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Unbounded.lean#L714-L840
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Unbounded.lean#L714-L840

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

theorem PVM.ofReal_norm_sq_integral_sub_unboundedIntegral (E_pvm : PVM E)
    (f : ℝ → ℂ) (hf : Measurable f) (hbdd : ∃ C, ∀ r, ‖f r‖ ≤ C)
    (g : ℝ → ℂ) (hg : Measurable g)
    (x : (E_pvm.unboundedIntegral g hg).domain) :
    ENNReal.ofReal
        (‖E_pvm.integral f hf hbdd (x : E) - E_pvm.unboundedIntegral g hg x‖ ^ 2) =
      ∫⁻ r, ‖f r - g r‖₊ ^ 2 ∂(E_pvm.scalarMeasure (x : E)) := by sorry
