-- Prove2me | Theorems.Thm_PVM_proj_biUnion_finset
-- name    : PVM.proj_biUnion_finset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:52:37.002368+00:00
-- url     : https://prove2.me/theorems/1bc134d0-c4ce-4366-bba0-d38d05238533
-- title:
--   PVM: proj bi Union finset
-- statement:
--   A PVM sends a finite pairwise-disjoint union of measurable sets to the sum of their
--   projections.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Basic.lean#L135-L161
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Basic.lean#L135-L161

import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Definitions.Def_Spectral_PVM_Basic
set_option autoImplicit false
open Function
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem PVM.proj_biUnion_finset {I : Type*} (E_pvm : PVM E)
    (s : Finset I) (A : I → Set ℝ) (hmeas : ∀ i ∈ s, MeasurableSet (A i))
    (hpair : (↑s : Set I).PairwiseDisjoint A) :
    E_pvm.proj (⋃ i ∈ (↑s : Set I), A i) = ∑ i ∈ s, E_pvm.proj (A i) := by sorry
