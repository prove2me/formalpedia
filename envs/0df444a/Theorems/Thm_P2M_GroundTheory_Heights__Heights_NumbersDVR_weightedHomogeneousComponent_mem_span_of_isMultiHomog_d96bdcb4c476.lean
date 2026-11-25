-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_weightedHomogeneousComponent_mem_span_of_isMultiHomog_d96bdcb4c476
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_weightedHomogeneousComponent_mem_span_of_isMultiHomog_d96bdcb4c476
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:12:10.867766+00:00
-- url     : https://prove2.me/theorems/72b6aecd-b571-44bc-ab21-d92f8b84695b
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR weighted Homogeneous Component mem span of is Multi Homog d96bdcb4c476: P2 M Ground Theory Heights  Heights Numbers DVR weighted Homogeneous Component m
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR weighted Homogeneous Component mem span of is Multi Homog d96bdcb4c476 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR weighted Homogeneous Component mem span of is Multi Homog d96bdcb4c476 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PCutByForm.lean#L13-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PCutByForm.lean#L13-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PCutByForm
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
noncomputable section
universe u

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_weightedHomogeneousComponent_mem_span_of_isMultiHomog_d96bdcb4c476 {R : Type*} [CommRing R] {K : Type*}
    [DecidableEq K] {ι : K → Type*} {s : MRing ι R} {c : K → ℕ} (hs : IsMultiHomog s c)
    {t : MRing ι R} (ht : t ∈ Ideal.span {s}) (b : K → ℕ) :
    weightedHomogeneousComponent (blockWeight ι) b t ∈ Ideal.span {s} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«weightedHomogeneousComponent_mem_span_of_isMultiHomog» := P2M_GroundTheory_Heights__Heights_NumbersDVR_weightedHomogeneousComponent_mem_span_of_isMultiHomog_d96bdcb4c476
