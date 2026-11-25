-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_CombExtendWord_exists_word_1ac480885857
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_CombExtendWord_exists_word_1ac480885857
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:05:18.862386+00:00
-- url     : https://prove2.me/theorems/c3d83c03-a306-4396-9cc1-fadb4c867d96
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Comb Extend Word exists word 1ac480885857: P2 M Ground Theory Heights  Heights Rest Terms Comb Extend Word exists word 1ac480885857
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Comb Extend Word exists word 1ac480885857 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Comb Extend Word exists word 1ac480885857 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PCombExtendWord.lean#L31-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PCombExtendWord.lean#L31-L97

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCombExtendWord
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open Finset Comb
noncomputable section
open scoped Classical
open GroundTheory.Heights₂.Heights.RestTerms.CombExtendWord

theorem P2M_GroundTheory_Heights__Heights_RestTerms_CombExtendWord_exists_word_1ac480885857 {m : ℕ} (h1 : CombPcntAppend.Statement) (μ : Fin m → ℕ) (hμ : Antitone μ) :
    ∀ (q : ℕ) (lam : Fin m → ℕ), Antitone lam → (∀ i, μ i ≤ lam i) →
      ∑ i, lam i = ∑ i, μ i + q →
        ∃ s : Fin q → Fin m, ∀ n, ∀ w ∈ latticeWords n μ,
          Fin.append w s ∈ latticeWords (n + q) lam := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«CombExtendWord».«exists_word» := P2M_GroundTheory_Heights__Heights_RestTerms_CombExtendWord_exists_word_1ac480885857
