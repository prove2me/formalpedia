-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Schur_det_hMatrix_staircase_8f257c117f9e
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Schur_det_hMatrix_staircase_8f257c117f9e
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:20:37.490075+00:00
-- url     : https://prove2.me/theorems/df70f2c2-58fa-4df8-8307-966c0007bf6b
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Schur det h Matrix staircase 8f257c117f9e: P2 M Ground Theory Heights  Heights Rest Terms Schur det h Matrix staircase 8f257c117f9e
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Schur det h Matrix staircase 8f257c117f9e construction uses the P2 M Ground Theory Heights  Heights Rest Terms Schur det h Matrix staircase 8f257c117f9e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/JacobiTrudi.lean#L188-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/JacobiTrudi.lean#L188-L201

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Schur_det_hMatrix_staircase_8f257c117f9e :
    (hMatrix (fun i : Fin m => m - 1 - (i : ℕ))).det = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Schur».«det_hMatrix_staircase» := P2M_GroundTheory_Heights__Heights_RestTerms_Schur_det_hMatrix_staircase_8f257c117f9e
