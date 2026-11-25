-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Schur_sum_hsymm_mul_coeff_omitProduct_8c99bd9e1f3f
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Schur_sum_hsymm_mul_coeff_omitProduct_8c99bd9e1f3f
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:20:47.449227+00:00
-- url     : https://prove2.me/theorems/520a9309-8d8c-4bd6-9737-b7178f9a243f
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Schur sum hsymm mul coeff omit Product 8c99bd9e1f3f: P2 M Ground Theory Heights  Heights Rest Terms Schur sum hsymm mul coeff omit Product 8c99bd9e1f3f
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Schur sum hsymm mul coeff omit Product 8c99bd9e1f3f construction uses the P2 M Ground Theory Heights  Heights Rest Terms Schur sum hsymm mul coeff omit Product 8c99bd9e1f3f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/JacobiTrudi.lean#L107-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/JacobiTrudi.lean#L107-L149

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Schur_sum_hsymm_mul_coeff_omitProduct_8c99bd9e1f3f (j : σ) (α : ℕ) :
    ∑ c ∈ range (Fintype.card σ), PowerSeries.coeff c (omitProduct j) *
      (if c ≤ α then hsymm σ ℚ (α - c) else 0) = X j ^ α := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Schur».«sum_hsymm_mul_coeff_omitProduct» := P2M_GroundTheory_Heights__Heights_RestTerms_Schur_sum_hsymm_mul_coeff_omitProduct_8c99bd9e1f3f
