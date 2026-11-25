-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_SchCompleteGenerating_coeff_prod_geomSeries_eval_8ca3da264bb5
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_SchCompleteGenerating_coeff_prod_geomSeries_eval_8ca3da264bb5
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:20:47.156433+00:00
-- url     : https://prove2.me/theorems/2342826f-fc2d-4e1f-8b3e-8cc1c3945d8c
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Sch Complete Generating coeff prod geom Series eval 8ca3da264bb5: P2 M Ground Theory Heights  Heights Rest Terms Sch Complete Generating coeff prod geom
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Sch Complete Generating coeff prod geom Series eval 8ca3da264bb5 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Sch Complete Generating coeff prod geom Series eval 8ca3da264bb5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchCompleteGenerating.lean#L15-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchCompleteGenerating.lean#L15-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchCompleteGenerating
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.SchCompleteGenerating

theorem P2M_GroundTheory_Heights__Heights_RestTerms_SchCompleteGenerating_coeff_prod_geomSeries_eval_8ca3da264bb5 {N : ℕ} (y : Fin N → ℂ) (n : ℕ) :
    PowerSeries.coeff n (∏ i : Fin N, Schur.geomSeries (y i)) =
      aeval y (hsymm (Fin N) ℚ n) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«SchCompleteGenerating».«coeff_prod_geomSeries_eval» := P2M_GroundTheory_Heights__Heights_RestTerms_SchCompleteGenerating_coeff_prod_geomSeries_eval_8ca3da264bb5
