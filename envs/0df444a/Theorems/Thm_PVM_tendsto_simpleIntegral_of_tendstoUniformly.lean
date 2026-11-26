-- Prove2me | Theorems.Thm_PVM_tendsto_simpleIntegral_of_tendstoUniformly
-- name    : PVM.tendsto_simpleIntegral_of_tendstoUniformly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:55:04.682623+00:00
-- url     : https://prove2.me/theorems/dfaa32d8-6e0e-4f41-9ac6-03b46af67368
-- title:
--   PVM: tendsto simple Integral of tendsto Uniformly
-- statement:
--   Spectral sums of any uniformly convergent simple approximation converge to the bounded
--   spectral integral. In particular, the limit is independent of the chosen bound and approximation
--   sequence.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Integral.lean#L545-L582
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Integral.lean#L545-L582

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

theorem PVM.tendsto_simpleIntegral_of_tendstoUniformly (E_pvm : PVM E)
    (f : ℝ → ℂ) (hf : Measurable f) (hbdd : ∃ C, ∀ t, ‖f t‖ ≤ C)
    (s : ℕ → SimpleFunc ℝ ℂ)
    (hs : TendstoUniformly (fun n t => s n t) f Filter.atTop) :
    Filter.Tendsto (fun n => E_pvm.simpleIntegral (s n))
      Filter.atTop (nhds (E_pvm.integral f hf hbdd)) := by sorry
