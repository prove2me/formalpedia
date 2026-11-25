-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_entries_bounded_of_conj_spanning_bounded__a0549da12fe9
-- name    : P2M_GlobalTheory_T_entries_bounded_of_conj_spanning_bounded__a0549da12fe9
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:09:45.384558+00:00
-- url     : https://prove2.me/theorems/8531eb4a-6f88-45c8-a9c5-0360d8f0b5c0
-- title:
--   P2 M Global Theory T entries bounded of conj spanning bounded  a0549da12fe9: P2 M Global Theory T entries bounded of conj spanning bounded  a0549da12fe9
-- statement:
--   The P2 M Global Theory T entries bounded of conj spanning bounded  a0549da12fe9 construction uses the P2 M Global Theory T entries bounded of conj spanning bounded  a0549da12fe9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/EntriesBoundedOfConjSpanningBoundedStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/EntriesBoundedOfConjSpanningBoundedStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_EntriesBoundedOfConjSpanningBounded
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_EntriesBoundedOfConjSpanningBoundedStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_entries_bounded_of_conj_spanning_bounded__a0549da12fe9 : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Type) [Fintype σ] (g : σ → Matrix ι ι ℂ), Submodule.span ℂ (Set.range g) = ⊤ → ∀ C : ℝ, ∃ C' : ℝ, ∀ P : Matrix ι ι ℂ, P.det = 1 → (∀ s i j, ‖(P * g s * P⁻¹) i j‖ ≤ C) → ∀ i j, ‖P i j‖ ≤ C' := by sorry

alias «GlobalTheory».«T».«entries_bounded_of_conj_spanning_bounded'» := P2M_GlobalTheory_T_entries_bounded_of_conj_spanning_bounded__a0549da12fe9
