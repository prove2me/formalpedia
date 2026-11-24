-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_component_not_mem_53dbbac47368
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_component_not_mem_53dbbac47368
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:34:48.271887+00:00
-- url     : https://prove2.me/theorems/23358ba9-dcf6-45e2-aebd-c81353ebdcaa
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR exists component not mem 53dbbac47368: P2 M Ground Theory Heights  Heights Numbers DVR exists component not mem 53dbbac47368
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR exists component not mem 53dbbac47368 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR exists component not mem 53dbbac47368 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PRepresentative.lean#L28-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PRepresentative.lean#L28-L35

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PRepresentative
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
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_component_not_mem_53dbbac47368 {H : Ideal (MRing ι R)} {x : MRing ι R} (hx : x ∉ H) :
    ∃ e : K → ℕ, weightedHomogeneousComponent (blockWeight ι) e x ∉ H := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«exists_component_not_mem» := P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_component_not_mem_53dbbac47368
