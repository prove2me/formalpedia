-- Prove2me | Theorems.Thm_PVM_proj_fiber_mul_proj_fiber
-- name    : PVM.proj_fiber_mul_proj_fiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:55:15.847403+00:00
-- url     : https://prove2.me/theorems/073688a6-493d-5c8d-baff-e680b80f6240
-- title:
--   PVM: proj fiber mul proj fiber
-- statement:
--   Projections onto two distinct fibers of a simple function multiply to zero.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Integral.lean#L139-L150
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Integral.lean#L139-L150

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

theorem PVM.proj_fiber_mul_proj_fiber (E_pvm : PVM E) (f : SimpleFunc ℝ ℂ)
    {z w : ℂ} (hzw : z ≠ w) :
    E_pvm.proj (f ⁻¹' {z}) * E_pvm.proj (f ⁻¹' {w}) = 0 := by sorry
