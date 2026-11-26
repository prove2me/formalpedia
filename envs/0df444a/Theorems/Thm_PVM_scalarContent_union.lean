-- Prove2me | Theorems.Thm_PVM_scalarContent_union
-- name    : PVM.scalarContent_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:01:14.864417+00:00
-- url     : https://prove2.me/theorems/6d44ab29-ce08-432e-8306-3c0cba1b69d2
-- title:
--   PVM: scalar Content union
-- statement:
--   Scalar PVM content is additive on disjoint measurable sets.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Unbounded.lean#L49-L56
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Unbounded.lean#L49-L56

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

theorem PVM.scalarContent_union (E_pvm : PVM E) (x : E) {S T : Set ℝ}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hdisj : Disjoint S T) :
    E_pvm.scalarContent x (S ∪ T) =
      E_pvm.scalarContent x S + E_pvm.scalarContent x T := by sorry
