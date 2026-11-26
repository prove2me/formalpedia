-- Prove2me | Theorems.Thm_PVM_sum_proj_preimage
-- name    : PVM.sum_proj_preimage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:55:02.175814+00:00
-- url     : https://prove2.me/theorems/2f95f881-7835-574b-b1c5-0c8b64698b10
-- title:
--   PVM: sum proj preimage
-- statement:
--   The projections of finitely many fibers add to the projection of their union.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Integral.lean#L30-L61
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Integral.lean#L30-L61

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

theorem PVM.sum_proj_preimage (E_pvm : PVM E) {β : Type*}
    (f : SimpleFunc ℝ β) (s : Finset β) :
    ∑ y ∈ s, E_pvm.proj (f ⁻¹' {y}) = E_pvm.proj (f ⁻¹' (↑s : Set β)) := by sorry
