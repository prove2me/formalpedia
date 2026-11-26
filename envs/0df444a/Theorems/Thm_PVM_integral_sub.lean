-- Prove2me | Theorems.Thm_PVM_integral_sub
-- name    : PVM.integral_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:55:48.434006+00:00
-- url     : https://prove2.me/theorems/cc22eed2-dfee-442b-9844-94ba7078b70d
-- title:
--   PVM: integral sub
-- statement:
--   Bounded spectral integration preserves pointwise subtraction, independently of the bound
--   witnesses used in the three integrals.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Integral.lean#L696-L718
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Integral.lean#L696-L718

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

theorem PVM.integral_sub (E_pvm : PVM E)
    (f g : ℝ → ℂ) (hf : Measurable f) (hg : Measurable g)
    (hbddf : ∃ C, ∀ t, ‖f t‖ ≤ C) (hbddg : ∃ C, ∀ t, ‖g t‖ ≤ C)
    (hbddsub : ∃ C, ∀ t, ‖(f - g) t‖ ≤ C) :
    E_pvm.integral (f - g) (hf.sub hg) hbddsub =
      E_pvm.integral f hf hbddf - E_pvm.integral g hg hbddg := by sorry
