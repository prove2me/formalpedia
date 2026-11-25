-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundOfPrimeBound_hypotheses_inhabited_by_decomposition_f27fab3d581d
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundOfPrimeBound_hypotheses_inhabited_by_decomposition_f27fab3d581d
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:35:04.900281+00:00
-- url     : https://prove2.me/theorems/70f555ed-3d7e-499f-8088-7370bfbac79b
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Rest Bound Of Prime Bound hypotheses inhabited by decomposition f27fab3d581d: P2 M Ground Theory Heights  Heights Rest Terms Rest Bound Of Prime Bound hy
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Rest Bound Of Prime Bound hypotheses inhabited by decomposition f27fab3d581d construction uses the P2 M Ground Theory Heights  Heights Rest Terms Rest Bound Of Prime Bound hypotheses inhabited by decomposition f27fab3d581d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/InhabitantsElem.lean#L57-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/InhabitantsElem.lean#L57-L114

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsElem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Inhabitants
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Elementary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_InhabitantsElem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundOfPrimeBound_hypotheses_inhabited_by_decomposition_f27fab3d581d
    (s : ℕ → ℕ → Fin 1 → Fin 1) (e : ℕ → ℕ → Fin 1 → ℕ → ℚ)
    (he : ∀ p n τ k, e p n τ k = 1 ∨ e p n τ k = -1) :
    4 * ((1 : ℕ) : ℝ) * ((1 + 1 : ℕ) : ℝ) ^ 2 ≤ 16 ∧
    ∀ p : ℕ, p.Prime → (16 : ℝ) < p →
      |restPrimeModel 1 1 1 .last inhQ s e p| ≤
        1.5 * ((1 : ℕ) : ℝ) * (restX 1 1 : ℝ) * (Real.log p / (p : ℝ) ^ 2) *
          ((1 * (1 * 1) + 1 : ℕ) : ℝ) * |(fibreDegree 1 1 1 .last : ℝ)| := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«RestBoundOfPrimeBound».«hypotheses_inhabited_by_decomposition» := P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundOfPrimeBound_hypotheses_inhabited_by_decomposition_f27fab3d581d
