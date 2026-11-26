-- Prove2me | Theorems.Thm_PVM_inner_simpleIntegral_self
-- name    : PVM.inner_simpleIntegral_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:01:16.3608+00:00
-- url     : https://prove2.me/theorems/86aee38c-2457-413c-8fe8-494ba6e82d28
-- title:
--   PVM: inner simple Integral self
-- statement:
--   Diagonal matrix coefficients of simple spectral integrals are scalar integrals.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Unbounded.lean#L130-L173
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Unbounded.lean#L130-L173

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

theorem PVM.inner_simpleIntegral_self (E_pvm : PVM E)
    (f : SimpleFunc ℝ ℂ) (x : E) :
    @inner ℂ E _ x (E_pvm.simpleIntegral f x) =
      ∫ t, f t ∂(E_pvm.scalarMeasure x) := by sorry
