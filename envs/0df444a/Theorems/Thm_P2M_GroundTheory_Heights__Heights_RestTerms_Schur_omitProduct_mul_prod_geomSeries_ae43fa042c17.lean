-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Schur_omitProduct_mul_prod_geomSeries_ae43fa042c17
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Schur_omitProduct_mul_prod_geomSeries_ae43fa042c17
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:20:33.513897+00:00
-- url     : https://prove2.me/theorems/f4ef84ec-d397-49f0-9dbd-6f4cb7fe9cd8
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Schur omit Product mul prod geom Series ae43fa042c17: P2 M Ground Theory Heights  Heights Rest Terms Schur omit Product mul prod geom Series ae43fa042c17
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Schur omit Product mul prod geom Series ae43fa042c17 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Schur omit Product mul prod geom Series ae43fa042c17 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/JacobiTrudi.lean#L93-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/JacobiTrudi.lean#L93-L98

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Schur_omitProduct_mul_prod_geomSeries_ae43fa042c17 (j : σ) :
    omitProduct j * ∏ i : σ, geomSeries (X i : MvPolynomial σ ℚ) = geomSeries (X j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Schur».«omitProduct_mul_prod_geomSeries» := P2M_GroundTheory_Heights__Heights_RestTerms_Schur_omitProduct_mul_prod_geomSeries_ae43fa042c17
