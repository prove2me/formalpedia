-- Prove2me | Theorems.Thm_PVM_simpleIntegral_map
-- name    : PVM.simpleIntegral_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:54:56.913352+00:00
-- url     : https://prove2.me/theorems/da5764b0-3621-5911-9030-d1a7ee47423d
-- title:
--   PVM: simple Integral map
-- statement:
--   Reindexing a simple function groups the projections of fibers with the same new value.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Integral.lean#L64-L75
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Integral.lean#L64-L75

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

theorem PVM.simpleIntegral_map (E_pvm : PVM E) {β : Type*}
    (f : SimpleFunc ℝ β) (g : β → ℂ) :
    E_pvm.simpleIntegral (f.map g) =
      ∑ y ∈ f.range, g y • E_pvm.proj (f ⁻¹' {y}) := by sorry
