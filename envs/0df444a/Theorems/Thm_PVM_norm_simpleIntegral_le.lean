-- Prove2me | Theorems.Thm_PVM_norm_simpleIntegral_le
-- name    : PVM.norm_simpleIntegral_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:55:00.528722+00:00
-- url     : https://prove2.me/theorems/b557c595-fcc8-4802-890d-134a405d048f
-- title:
--   PVM: norm simple Integral le
-- statement:
--   A uniform bound for a simple function bounds the norm of its spectral sum.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Integral.lean#L236-L283
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Integral.lean#L236-L283

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

theorem PVM.norm_simpleIntegral_le (E_pvm : PVM E) (f : SimpleFunc ℝ ℂ) {C : ℝ}
    (hbdd : ∀ t, ‖f t‖ ≤ C) : ‖E_pvm.simpleIntegral f‖ ≤ C := by sorry
