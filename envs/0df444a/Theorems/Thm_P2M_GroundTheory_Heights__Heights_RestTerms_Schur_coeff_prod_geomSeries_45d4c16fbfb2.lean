-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Schur_coeff_prod_geomSeries_45d4c16fbfb2
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Schur_coeff_prod_geomSeries_45d4c16fbfb2
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:20:34.257887+00:00
-- url     : https://prove2.me/theorems/389f9047-ffcf-4824-b492-6ad70b49729d
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Schur coeff prod geom Series 45d4c16fbfb2: P2 M Ground Theory Heights  Heights Rest Terms Schur coeff prod geom Series 45d4c16fbfb2
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Schur coeff prod geom Series 45d4c16fbfb2 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Schur coeff prod geom Series 45d4c16fbfb2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/JacobiTrudi.lean#L85-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/JacobiTrudi.lean#L85-L88

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Schur_coeff_prod_geomSeries_45d4c16fbfb2 (n : ℕ) :
    PowerSeries.coeff n (∏ i : σ, geomSeries (X i : MvPolynomial σ ℚ)) = hsymm σ ℚ n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Schur».«coeff_prod_geomSeries» := P2M_GroundTheory_Heights__Heights_RestTerms_Schur_coeff_prod_geomSeries_45d4c16fbfb2
