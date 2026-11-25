-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_SchCompleteGenerating_coe_prod_one_sub_46d3c6e30d7b
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_SchCompleteGenerating_coe_prod_one_sub_46d3c6e30d7b
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:56:43.03137+00:00
-- url     : https://prove2.me/theorems/ff6887e3-e366-5e12-a96e-fc97ac1ecaad
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Sch Complete Generating coe prod one sub 46d3c6e30d7b: P2 M Ground Theory Heights  Heights Rest Terms Sch Complete Generating coe prod one sub 46d3c6e30d
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Sch Complete Generating coe prod one sub 46d3c6e30d7b construction uses the P2 M Ground Theory Heights  Heights Rest Terms Sch Complete Generating coe prod one sub 46d3c6e30d7b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchCompleteGenerating.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchCompleteGenerating.lean#L22-L26

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_SchCompleteGenerating_coe_prod_one_sub_46d3c6e30d7b {N : ℕ} (y : Fin N → ℂ) :
    ((∏ i : Fin N, (1 - Polynomial.C (y i) * Polynomial.X) : Polynomial ℂ) : PowerSeries ℂ) =
      ∏ i : Fin N, (1 - PowerSeries.C (y i) * PowerSeries.X) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«SchCompleteGenerating».«coe_prod_one_sub» := P2M_GroundTheory_Heights__Heights_RestTerms_SchCompleteGenerating_coe_prod_one_sub_46d3c6e30d7b
