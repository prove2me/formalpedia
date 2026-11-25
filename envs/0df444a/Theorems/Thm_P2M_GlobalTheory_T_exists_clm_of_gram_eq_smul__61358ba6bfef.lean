-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_clm_of_gram_eq_smul__61358ba6bfef
-- name    : P2M_GlobalTheory_T_exists_clm_of_gram_eq_smul__61358ba6bfef
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:26:26.076328+00:00
-- url     : https://prove2.me/theorems/fdaff0d6-6d81-4c8a-9564-9377cb0b99b6
-- title:
--   P2 M Global Theory T exists clm of gram eq smul  61358ba6bfef: P2 M Global Theory T exists clm of gram eq smul  61358ba6bfef
-- statement:
--   The P2 M Global Theory T exists clm of gram eq smul  61358ba6bfef construction uses the P2 M Global Theory T exists clm of gram eq smul  61358ba6bfef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsClmOfGramEqSmulStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsClmOfGramEqSmulStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsClmOfGramEqSmul
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsClmOfGramEqSmulStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_clm_of_gram_eq_smul__61358ba6bfef : ∀ {α Hs E : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (u : α → Hs) (f : α → E) (K : ℝ), (∀ a b, ⟪f a, f b⟫_ℂ = (K : ℂ) * ⟪u a, u b⟫_ℂ) → Dense (Submodule.span ℂ (Set.range u) : Set Hs) → ∃ A : Hs →L[ℂ] E, ∀ a, A (u a) = f a := by sorry

alias «GlobalTheory».«T».«exists_clm_of_gram_eq_smul'» := P2M_GlobalTheory_T_exists_clm_of_gram_eq_smul__61358ba6bfef
