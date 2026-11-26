-- Prove2me | Theorems.Thm_PVM_sum_proj_fiber_eq_one
-- name    : PVM.sum_proj_fiber_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:55:22.17193+00:00
-- url     : https://prove2.me/theorems/b68ceea0-355c-4ca0-a04c-fdf1ee7b8977
-- title:
--   PVM: sum proj fiber eq one
-- statement:
--   The projections of the fibers of a simple function sum to the identity.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Integral.lean#L115-L136
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Integral.lean#L115-L136

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

theorem PVM.sum_proj_fiber_eq_one (E_pvm : PVM E) (f : SimpleFunc ℝ ℂ) :
    (∑ z ∈ f.range, E_pvm.proj (f ⁻¹' {z})) = 1 := by sorry
