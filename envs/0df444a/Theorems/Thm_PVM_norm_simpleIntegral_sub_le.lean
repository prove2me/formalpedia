-- Prove2me | Theorems.Thm_PVM_norm_simpleIntegral_sub_le
-- name    : PVM.norm_simpleIntegral_sub_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:54:58.820686+00:00
-- url     : https://prove2.me/theorems/bad1a816-28b0-4ae7-9908-53499323edd9
-- title:
--   PVM: norm simple Integral sub le
-- statement:
--   Uniform distance of simple functions controls the operator norm of their spectral sums.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Integral.lean#L286-L292
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Integral.lean#L286-L292

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

theorem PVM.norm_simpleIntegral_sub_le (E_pvm : PVM E) (f g : SimpleFunc ℝ ℂ) {C : ℝ}
    (hbdd : ∀ t, ‖f t - g t‖ ≤ C) :
    ‖E_pvm.simpleIntegral f - E_pvm.simpleIntegral g‖ ≤ C := by sorry
