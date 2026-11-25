-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_conj_harm_of_span__62df867434b0
-- name    : P2M_GlobalTheory_T_exists_conj_harm_of_span__62df867434b0
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:11:33.557809+00:00
-- url     : https://prove2.me/theorems/bc062b1a-6e6a-4b56-a043-57c8ce3af29e
-- title:
--   P2 M Global Theory T exists conj harm of span  62df867434b0: P2 M Global Theory T exists conj harm of span  62df867434b0
-- statement:
--   The P2 M Global Theory T exists conj harm of span  62df867434b0 construction uses the P2 M Global Theory T exists conj harm of span  62df867434b0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsConjHarmOfSpanStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsConjHarmOfSpanStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsConjHarmOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsConjHarmOfSpanStatement
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

theorem P2M_GlobalTheory_T_exists_conj_harm_of_span__62df867434b0 : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Type) [Fintype σ] (τ : σ ≃ σ) (g : σ → Matrix ι ι ℂ), (∀ s, g (τ s) * g s = 1) → Submodule.span ℂ (Set.range g) = ⊤ → ∃ P : Matrix ι ι ℂ, IsUnit P.det ∧ Harm (fun s => P * g s * P⁻¹) := by sorry

alias «GlobalTheory».«T».«exists_conj_harm_of_span'» := P2M_GlobalTheory_T_exists_conj_harm_of_span__62df867434b0
