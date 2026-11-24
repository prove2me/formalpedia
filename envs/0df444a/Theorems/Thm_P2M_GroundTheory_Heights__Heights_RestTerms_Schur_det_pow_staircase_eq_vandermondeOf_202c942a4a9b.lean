-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Schur_det_pow_staircase_eq_vandermondeOf_202c942a4a9b
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Schur_det_pow_staircase_eq_vandermondeOf_202c942a4a9b
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:26:28.785855+00:00
-- url     : https://prove2.me/theorems/2bd6fb60-9f18-470c-8db5-94193f3d4229
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Schur det pow staircase eq vandermonde Of 202c942a4a9b: P2 M Ground Theory Heights  Heights Rest Terms Schur det pow staircase eq vandermonde Of 202c942a
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Schur det pow staircase eq vandermonde Of 202c942a4a9b construction uses the P2 M Ground Theory Heights  Heights Rest Terms Schur det pow staircase eq vandermonde Of 202c942a4a9b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/JacobiTrudi.lean#L221-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/JacobiTrudi.lean#L221-L253

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Schur_det_pow_staircase_eq_vandermondeOf_202c942a4a9b {R : Type*} [CommRing R] (v : Fin m → R) :
    (Matrix.of fun i j : Fin m => v j ^ (m - 1 - (i : ℕ))).det = vandermondeOf v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Schur».«det_pow_staircase_eq_vandermondeOf» := P2M_GroundTheory_Heights__Heights_RestTerms_Schur_det_pow_staircase_eq_vandermondeOf_202c942a4a9b
