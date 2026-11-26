-- Prove2me | Theorems.Thm_PVM_monotone
-- name    : PVM.monotone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:52:31.594864+00:00
-- url     : https://prove2.me/theorems/982525a5-97c5-5792-9d6a-1c73ecf9dd46
-- title:
--   PVM: monotone
-- statement:
--   Inclusion of measurable sets makes the real scalar quadratic form of a PVM projection
--   monotone.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Basic.lean#L40-L62
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Basic.lean#L40-L62

import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Definitions.Def_Spectral_PVM_Basic
set_option autoImplicit false
open Function
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem PVM.monotone (E_pvm : PVM E) {S T : Set ℝ}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (h : S ⊆ T) (x : E) :
    (@inner ℂ E _ (E_pvm.proj S x) x).re ≤ (@inner ℂ E _ (E_pvm.proj T x) x).re := by sorry
