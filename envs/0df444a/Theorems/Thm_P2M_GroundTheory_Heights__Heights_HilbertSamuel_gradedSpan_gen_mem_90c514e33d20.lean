-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_gradedSpan_gen_mem_90c514e33d20
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_gradedSpan_gen_mem_90c514e33d20
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:18:46.819991+00:00
-- url     : https://prove2.me/theorems/541a4b60-e318-46a7-837f-85441d89a774
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel graded Span gen mem 90c514e33d20: P2 M Ground Theory Heights  Heights Hilbert Samuel graded Span gen mem 90c514e33d20
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel graded Span gen mem 90c514e33d20 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel graded Span gen mem 90c514e33d20 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsSerreGraded.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsSerreGraded.lean#L17-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSerreGraded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_gradedSpan_gen_mem_90c514e33d20 {Ω : Type*} [CommRing Ω] {q r : ℕ} (w : Fin q → Ω) (d : Fin r → ℕ) (t : Fin r → Ω)
    (l : Fin r) (μ : Fin q → ℕ) : t l * ∏ j, w j ^ μ j ∈ gradedSpan w d t (d l + ∑ j, μ j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«gradedSpan_gen_mem» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_gradedSpan_gen_mem_90c514e33d20
