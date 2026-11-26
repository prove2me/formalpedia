-- Prove2me | Theorems.Thm_PVM_norm_sq_simpleIntegral
-- name    : PVM.norm_sq_simpleIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:55:23.389852+00:00
-- url     : https://prove2.me/theorems/ee8196bd-63b1-5b4c-a79b-cab3108a75fb
-- title:
--   PVM: norm sq simple Integral
-- statement:
--   The squared norm of a simple spectral sum is the weighted sum over its fibers.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Integral.lean#L209-L233
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Integral.lean#L209-L233

import Definitions.Def_Spectral_PVM_Basic
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Topology.UniformSpace.Dini
import Definitions.Def_Spectral_PVM_Integral
set_option autoImplicit false
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem PVM.norm_sq_simpleIntegral (E_pvm : PVM E) (f : SimpleFunc ℝ ℂ) (x : E) :
    ‖E_pvm.simpleIntegral f x‖ ^ 2 =
      ∑ z ∈ f.range, ‖z‖ ^ 2 * (@inner ℂ E _ (E_pvm.proj (f ⁻¹' {z}) x) x).re := by sorry
