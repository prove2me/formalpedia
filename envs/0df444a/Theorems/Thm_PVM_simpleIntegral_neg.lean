-- Prove2me | Theorems.Thm_PVM_simpleIntegral_neg
-- name    : PVM.simpleIntegral_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:55:16.090072+00:00
-- url     : https://prove2.me/theorems/3d50bb7d-2522-52a9-b585-38562ca6e080
-- title:
--   PVM: simple Integral neg
-- statement:
--   Simple spectral integration preserves negation.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Integral.lean#L100-L106
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Integral.lean#L100-L106

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

theorem PVM.simpleIntegral_neg (E_pvm : PVM E) (f : SimpleFunc ℝ ℂ) :
    E_pvm.simpleIntegral (-f) = -E_pvm.simpleIntegral f := by sorry
