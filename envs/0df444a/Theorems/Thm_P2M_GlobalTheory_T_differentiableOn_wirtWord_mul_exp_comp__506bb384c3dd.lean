-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_differentiableOn_wirtWord_mul_exp_comp__506bb384c3dd
-- name    : P2M_GlobalTheory_T_differentiableOn_wirtWord_mul_exp_comp__506bb384c3dd
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:10:12.881713+00:00
-- url     : https://prove2.me/theorems/87686d95-5ffa-4546-b6a9-10b40902f6a0
-- title:
--   P2 M Global Theory T differentiable On wirt Word mul exp comp  506bb384c3dd: P2 M Global Theory T differentiable On wirt Word mul exp comp  506bb384c3dd
-- statement:
--   The P2 M Global Theory T differentiable On wirt Word mul exp comp  506bb384c3dd construction uses the P2 M Global Theory T differentiable On wirt Word mul exp comp  506bb384c3dd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DifferentiableOnWirtWordMulExpCompStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DifferentiableOnWirtWordMulExpCompStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableOnWirtWordMulExpComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableRisingS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableOnWirtWordMulExpCompStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_differentiableOn_wirtWord_mul_exp_comp__506bb384c3dd : ∀ (Φ I : Type) [Fintype Φ] [Fintype I] (U : Set (I → ℂ)) (V : Set (Φ → ℂ)) (D : Set ℂ) (G : ℂ → (Φ → ℂ) → ℂ) (t : (I → ℂ) → Φ → ℂ) (b l : (I → ℂ) → ℂ), IsOpen U → IsOpen V → Set.MapsTo t U V → ContDiffOn ℝ ∞ t U → ContDiffOn ℝ ∞ b U → ContDiffOn ℝ ∞ l U → (∀ σ ∈ D, ContDiffOn ℝ ∞ (G σ) V) → (∀ w : List (Φ × Bool), ∀ y ∈ V, DifferentiableOn ℂ (fun σ => wirtWord w (G σ) y) D) → ∀ w : List (I × Bool), ∀ z ∈ U, DifferentiableOn ℂ (fun σ => wirtWord w (fun z' => b z' * Complex.exp (-σ * l z') * G σ (t z')) z) D := by sorry

alias «GlobalTheory».«T».«differentiableOn_wirtWord_mul_exp_comp'» := P2M_GlobalTheory_T_differentiableOn_wirtWord_mul_exp_comp__506bb384c3dd
