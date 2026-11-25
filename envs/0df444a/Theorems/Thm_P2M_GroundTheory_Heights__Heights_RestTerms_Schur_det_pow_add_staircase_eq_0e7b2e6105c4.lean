-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Schur_det_pow_add_staircase_eq_0e7b2e6105c4
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Schur_det_pow_add_staircase_eq_0e7b2e6105c4
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:26:28.465299+00:00
-- url     : https://prove2.me/theorems/5d8e3cd3-cbcd-4e65-b069-fd5a8bf9e39a
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Schur det pow add staircase eq 0e7b2e6105c4: P2 M Ground Theory Heights  Heights Rest Terms Schur det pow add staircase eq 0e7b2e6105c4
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Schur det pow add staircase eq 0e7b2e6105c4 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Schur det pow add staircase eq 0e7b2e6105c4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/JacobiTrudi.lean#L322-L325
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/JacobiTrudi.lean#L322-L325

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Schur_det_pow_add_staircase_eq_0e7b2e6105c4 {m : ℕ} (lam : Fin m → ℕ) :
    (Matrix.of fun i j : Fin m => (X j : MvPolynomial (Fin m) ℚ) ^ (lam i + (m - 1 - (i : ℕ)))).det =
      schur (Fin m) lam * vandermondeOf (fun i : Fin m => (X i : MvPolynomial (Fin m) ℚ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Schur».«det_pow_add_staircase_eq» := P2M_GroundTheory_Heights__Heights_RestTerms_Schur_det_pow_add_staircase_eq_0e7b2e6105c4
