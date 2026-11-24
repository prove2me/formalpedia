-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Schur_hsymm_eq_sum_finsuppAntidiag_43772939f291
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Schur_hsymm_eq_sum_finsuppAntidiag_43772939f291
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:26:35.248948+00:00
-- url     : https://prove2.me/theorems/c3a561e5-690f-4401-a3f4-317536fd7936
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Schur hsymm eq sum finsupp Antidiag 43772939f291: P2 M Ground Theory Heights  Heights Rest Terms Schur hsymm eq sum finsupp Antidiag 43772939f291
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Schur hsymm eq sum finsupp Antidiag 43772939f291 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Schur hsymm eq sum finsupp Antidiag 43772939f291 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/JacobiTrudi.lean#L15-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/JacobiTrudi.lean#L15-L43

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
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Schur_hsymm_eq_sum_finsuppAntidiag_43772939f291 (n : ℕ) :
    hsymm σ ℚ n = ∑ l ∈ finsuppAntidiag (univ : Finset σ) n, ∏ i, (X i : MvPolynomial σ ℚ) ^ l i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Schur».«hsymm_eq_sum_finsuppAntidiag» := P2M_GroundTheory_Heights__Heights_RestTerms_Schur_hsymm_eq_sum_finsuppAntidiag_43772939f291
