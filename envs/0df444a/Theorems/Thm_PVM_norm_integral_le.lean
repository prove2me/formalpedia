-- Prove2me | Theorems.Thm_PVM_norm_integral_le
-- name    : PVM.norm_integral_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:55:35.492252+00:00
-- url     : https://prove2.me/theorems/68ec45df-a6e4-5715-8dfa-7f246274b741
-- title:
--   PVM: norm integral le
-- statement:
--   A pointwise bound on an integrand bounds the operator norm of its spectral integral.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Integral.lean#L593-L601
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Integral.lean#L593-L601

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

theorem PVM.norm_integral_le (E_pvm : PVM E)
    (f : ℝ → ℂ) (hf : Measurable f) {C : ℝ} (hbdd : ∀ t, ‖f t‖ ≤ C) :
    ‖E_pvm.integral f hf ⟨C, hbdd⟩‖ ≤ C := by sorry
