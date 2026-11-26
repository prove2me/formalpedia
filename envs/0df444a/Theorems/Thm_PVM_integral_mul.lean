-- Prove2me | Theorems.Thm_PVM_integral_mul
-- name    : PVM.integral_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:55:47.189065+00:00
-- url     : https://prove2.me/theorems/66070ad0-3d54-4116-b67e-a00c66c59bfe
-- title:
--   PVM: integral mul
-- statement:
--   Bounded spectral integration preserves pointwise multiplication.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Integral.lean#L672-L692
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Integral.lean#L672-L692

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

theorem PVM.integral_mul (E_pvm : PVM E)
    (f g : ℝ → ℂ) (hf : Measurable f) (hg : Measurable g)
    (hbddf : ∃ C, ∀ t, ‖f t‖ ≤ C) (hbddg : ∃ C, ∀ t, ‖g t‖ ≤ C)
    (hbddfg : ∃ C, ∀ t, ‖(f * g) t‖ ≤ C) :
    E_pvm.integral (f * g) (hf.mul hg) hbddfg =
      E_pvm.integral f hf hbddf * E_pvm.integral g hg hbddg := by sorry
