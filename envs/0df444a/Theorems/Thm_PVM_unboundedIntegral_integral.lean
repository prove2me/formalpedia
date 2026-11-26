-- Prove2me | Theorems.Thm_PVM_unboundedIntegral_integral
-- name    : PVM.unboundedIntegral_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:01:27.073179+00:00
-- url     : https://prove2.me/theorems/d1123bd7-9c96-46d3-bf93-fa82cbb0567f
-- title:
--   PVM: unbounded Integral integral
-- statement:
--   Unbounded spectral integration acts on bounded spectral-integral vectors by pointwise
--   multiplication, provided the product integrand is bounded.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Unbounded.lean#L1202-L1240
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Unbounded.lean#L1202-L1240

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

theorem PVM.unboundedIntegral_integral
    (E_pvm : PVM E) (f : ℝ → ℂ) (hf : Measurable f)
    (hfBdd : ∃ C, ∀ r, ‖f r‖ ≤ C)
    (g : ℝ → ℂ) (hg : Measurable g)
    (hprodBdd : ∃ C, ∀ r, ‖(g * f) r‖ ≤ C) (x : E) :
    E_pvm.unboundedIntegral g hg
        ⟨E_pvm.integral f hf hfBdd x,
          E_pvm.integral_mem_domain_unboundedIntegral
            f hf hfBdd g hg hprodBdd x⟩ =
      E_pvm.integral (g * f) (hg.mul hf) hprodBdd x := by sorry
