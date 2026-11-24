-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GradedFrameCharacterisation_repr_sum_smul_c443a2f82c23
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_GradedFrameCharacterisation_repr_sum_smul_c443a2f82c23
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:57.535686+00:00
-- url     : https://prove2.me/theorems/18190d21-82c7-4cda-a44b-efb7142f8d8f
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Graded Frame Characterisation repr sum smul c443a2f82c23: P2 M Ground Theory Heights  Heights Numbers DVR Graded Frame Characterisation repr sum smul c4
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Graded Frame Characterisation repr sum smul c443a2f82c23 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Graded Frame Characterisation repr sum smul c443a2f82c23 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinGradedFrameIff.lean#L18-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinGradedFrameIff.lean#L18-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueSat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinGradedFrameIff
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
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
universe u v w
open GroundTheory.Heights₂.Heights.NumbersDVR.GradedFrameCharacterisation
variable {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_GradedFrameCharacterisation_repr_sum_smul_c443a2f82c23 {τ : Type*} [Fintype τ] (w : Module.Basis (Fin N) Ω E) (a : τ → Ω) (bb : τ → E)
    (j : Fin N) :
    w.repr (∑ q, a q • bb q) j = ∑ q, a q * w.repr (bb q) j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«GradedFrameCharacterisation».«repr_sum_smul» := P2M_GroundTheory_Heights__Heights_NumbersDVR_GradedFrameCharacterisation_repr_sum_smul_c443a2f82c23
