-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_pcnt_le_of_le_fec53aa30c0b
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Comb_pcnt_le_of_le_fec53aa30c0b
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:18:55.965842+00:00
-- url     : https://prove2.me/theorems/0a58ad66-61e8-5d7e-883c-3f5a6565f585
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Comb pcnt le of le fec53aa30c0b: P2 M Ground Theory Heights  Heights Rest Terms Comb pcnt le of le fec53aa30c0b
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Comb pcnt le of le fec53aa30c0b construction uses the P2 M Ground Theory Heights  Heights Rest Terms Comb pcnt le of le fec53aa30c0b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Lattice.lean#L46-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Lattice.lean#L46-L49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Lattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.Comb
open MvPolynomial Finset Equiv
noncomputable section
open scoped Classical
variable {m : ℕ}

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Comb_pcnt_le_of_le_fec53aa30c0b {n : ℕ} (w : Fin n → Fin m) {t t' : ℕ} (h : t ≤ t') (i : Fin m) :
    pcnt w t i ≤ pcnt w t' i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Comb».«pcnt_le_of_le» := P2M_GroundTheory_Heights__Heights_RestTerms_Comb_pcnt_le_of_le_fec53aa30c0b
