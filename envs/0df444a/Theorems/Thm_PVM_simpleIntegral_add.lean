-- Prove2me | Theorems.Thm_PVM_simpleIntegral_add
-- name    : PVM.simpleIntegral_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:55:29.642603+00:00
-- url     : https://prove2.me/theorems/dc669a99-a26d-4934-9e3e-6f67c4c95a58
-- title:
--   PVM: simple Integral add
-- statement:
--   Simple spectral integration preserves addition.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Integral.lean#L78-L97
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Integral.lean#L78-L97

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

theorem PVM.simpleIntegral_add (E_pvm : PVM E) (f g : SimpleFunc ℝ ℂ) :
    E_pvm.simpleIntegral (f + g) = E_pvm.simpleIntegral f + E_pvm.simpleIntegral g := by sorry
