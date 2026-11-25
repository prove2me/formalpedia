-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Schur_det_pow_add_staircase_fd8121b8213d
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Schur_det_pow_add_staircase_fd8121b8213d
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:20:38.152911+00:00
-- url     : https://prove2.me/theorems/cd77083d-7034-4bbf-8635-7ac503c152c7
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Schur det pow add staircase fd8121b8213d: P2 M Ground Theory Heights  Heights Rest Terms Schur det pow add staircase fd8121b8213d
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Schur det pow add staircase fd8121b8213d construction uses the P2 M Ground Theory Heights  Heights Rest Terms Schur det pow add staircase fd8121b8213d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/JacobiTrudi.lean#L203-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/JacobiTrudi.lean#L203-L219

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.Schur
open MvPolynomial Finset
noncomputable section
variable {m : ℕ}

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Schur_det_pow_add_staircase_fd8121b8213d (lam : Fin m → ℕ) :
    (Matrix.of fun i j : Fin m => (X j : MvPolynomial (Fin m) ℚ) ^ (lam i + (m - 1 - (i : ℕ)))).det =
      schur (Fin m) lam *
        (Matrix.of fun i j : Fin m => (X j : MvPolynomial (Fin m) ℚ) ^ (m - 1 - (i : ℕ))).det := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Schur».«det_pow_add_staircase» := P2M_GroundTheory_Heights__Heights_RestTerms_Schur_det_pow_add_staircase_fd8121b8213d
