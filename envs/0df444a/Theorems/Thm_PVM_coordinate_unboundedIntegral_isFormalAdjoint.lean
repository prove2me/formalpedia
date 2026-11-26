-- Prove2me | Theorems.Thm_PVM_coordinate_unboundedIntegral_isFormalAdjoint
-- name    : PVM.coordinate_unboundedIntegral_isFormalAdjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:01:12.827094+00:00
-- url     : https://prove2.me/theorems/d24e164a-102c-514d-946d-281f15ee0bca
-- title:
--   PVM: coordinate unbounded Integral is Formal Adjoint
-- statement:
--   Integration of the real coordinate against any PVM is a symmetric partial operator.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Unbounded.lean#L1388-L1394
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Unbounded.lean#L1388-L1394

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

theorem PVM.coordinate_unboundedIntegral_isFormalAdjoint (E_pvm : PVM E) :
    let A := E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
      Complex.continuous_ofReal.measurable
    A.IsFormalAdjoint A := by sorry
