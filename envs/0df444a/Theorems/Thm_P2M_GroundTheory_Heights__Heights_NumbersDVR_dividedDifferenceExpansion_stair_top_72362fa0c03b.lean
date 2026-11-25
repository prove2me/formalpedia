-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_dividedDifferenceExpansion_stair_top_72362fa0c03b
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_dividedDifferenceExpansion_stair_top_72362fa0c03b
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:09:57.321814+00:00
-- url     : https://prove2.me/theorems/edd57270-465b-4aa6-a3d3-817880f66cfe
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR divided Difference Expansion stair top 72362fa0c03b: P2 M Ground Theory Heights  Heights Numbers DVR divided Difference Expansion stair top 72362fa0c03b
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR divided Difference Expansion stair top 72362fa0c03b construction uses the P2 M Ground Theory Heights  Heights Numbers DVR divided Difference Expansion stair top 72362fa0c03b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinDivDiffExpansion.lean#L40-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinDivDiffExpansion.lean#L40-L41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinDivDiffExpansion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR.dividedDifferenceExpansion

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_dividedDifferenceExpansion_stair_top_72362fa0c03b {r : ℕ} (μ : Fin r →₀ ℕ) : stair μ r = ∏ j, X (Sum.inr j) ^ μ j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«dividedDifferenceExpansion».«stair_top» := P2M_GroundTheory_Heights__Heights_NumbersDVR_dividedDifferenceExpansion_stair_top_72362fa0c03b
