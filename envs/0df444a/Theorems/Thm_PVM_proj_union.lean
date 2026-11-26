-- Prove2me | Theorems.Thm_PVM_proj_union
-- name    : PVM.proj_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:52:26.725243+00:00
-- url     : https://prove2.me/theorems/932c1ab9-fc05-4b6e-b4a2-8bd97340e274
-- title:
--   PVM: proj union
-- statement:
--   A PVM sends the union of two disjoint measurable sets to the sum of their projections.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Basic.lean#L65-L131
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Basic.lean#L65-L131

import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Definitions.Def_Spectral_PVM_Basic
set_option autoImplicit false
open Function
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem PVM.proj_union (E_pvm : PVM E) {S T : Set ℝ}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hdisj : Disjoint S T) :
    E_pvm.proj (S ∪ T) = E_pvm.proj S + E_pvm.proj T := by sorry
