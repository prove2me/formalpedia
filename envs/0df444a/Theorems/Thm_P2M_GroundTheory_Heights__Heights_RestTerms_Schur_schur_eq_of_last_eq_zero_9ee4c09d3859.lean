-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Schur_schur_eq_of_last_eq_zero_9ee4c09d3859
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Schur_schur_eq_of_last_eq_zero_9ee4c09d3859
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:20:39.959956+00:00
-- url     : https://prove2.me/theorems/916beaaa-0daf-41fa-ac4b-e1fb131139e3
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Schur schur eq of last eq zero 9ee4c09d3859: P2 M Ground Theory Heights  Heights Rest Terms Schur schur eq of last eq zero 9ee4c09d3859
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Schur schur eq of last eq zero 9ee4c09d3859 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Schur schur eq of last eq zero 9ee4c09d3859 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/JacobiTrudi.lean#L264-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/JacobiTrudi.lean#L264-L281

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
variable (σ : Type*) [Fintype σ] [DecidableEq σ]

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Schur_schur_eq_of_last_eq_zero_9ee4c09d3859 {n : ℕ} (lam : Fin (n + 1) → ℕ) (h : lam (Fin.last n) = 0) :
    schur σ lam = schur σ (fun i : Fin n => lam i.castSucc) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Schur».«schur_eq_of_last_eq_zero» := P2M_GroundTheory_Heights__Heights_RestTerms_Schur_schur_eq_of_last_eq_zero_9ee4c09d3859
