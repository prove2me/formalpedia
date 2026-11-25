-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_dividedDifferenceExpansion_stair_zero_d0e94a0e87e2
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_dividedDifferenceExpansion_stair_zero_d0e94a0e87e2
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:10:52.785022+00:00
-- url     : https://prove2.me/theorems/bb81fd20-cb1a-476d-b744-e4ff72358f0c
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR divided Difference Expansion stair zero d0e94a0e87e2: P2 M Ground Theory Heights  Heights Numbers DVR divided Difference Expansion stair zero d0e94a0e87
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR divided Difference Expansion stair zero d0e94a0e87e2 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR divided Difference Expansion stair zero d0e94a0e87e2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinDivDiffExpansion.lean#L37-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinDivDiffExpansion.lean#L37-L38

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_dividedDifferenceExpansion_stair_zero_d0e94a0e87e2 {r : ℕ} (μ : Fin r →₀ ℕ) : stair μ 0 = ∏ j, X (Sum.inl j) ^ μ j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«dividedDifferenceExpansion».«stair_zero» := P2M_GroundTheory_Heights__Heights_NumbersDVR_dividedDifferenceExpansion_stair_zero_d0e94a0e87e2
