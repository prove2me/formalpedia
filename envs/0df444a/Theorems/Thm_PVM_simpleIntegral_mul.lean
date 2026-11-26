-- Prove2me | Theorems.Thm_PVM_simpleIntegral_mul
-- name    : PVM.simpleIntegral_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:55:19.754878+00:00
-- url     : https://prove2.me/theorems/bc731e76-a791-569c-82cb-31b089bd61ba
-- title:
--   PVM: simple Integral mul
-- statement:
--   Simple spectral integration preserves pointwise multiplication.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Integral.lean#L183-L188
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Integral.lean#L183-L188

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

theorem PVM.simpleIntegral_mul (E_pvm : PVM E) (f g : SimpleFunc ℝ ℂ) :
    E_pvm.simpleIntegral (f * g) = E_pvm.simpleIntegral f * E_pvm.simpleIntegral g := by sorry
