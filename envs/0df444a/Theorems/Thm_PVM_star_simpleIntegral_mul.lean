-- Prove2me | Theorems.Thm_PVM_star_simpleIntegral_mul
-- name    : PVM.star_simpleIntegral_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:55:27.353779+00:00
-- url     : https://prove2.me/theorems/30097ba4-29a8-5992-9ae7-f1884c9111ce
-- title:
--   PVM: star simple Integral mul
-- statement:
--   Multiplying a simple spectral sum by its adjoint removes all cross-fiber terms.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Integral.lean#L191-L206
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Integral.lean#L191-L206

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

theorem PVM.star_simpleIntegral_mul (E_pvm : PVM E) (f : SimpleFunc ℝ ℂ) :
    star (E_pvm.simpleIntegral f) * E_pvm.simpleIntegral f =
      ∑ z ∈ f.range, (star z * z) • E_pvm.proj (f ⁻¹' {z}) := by sorry
