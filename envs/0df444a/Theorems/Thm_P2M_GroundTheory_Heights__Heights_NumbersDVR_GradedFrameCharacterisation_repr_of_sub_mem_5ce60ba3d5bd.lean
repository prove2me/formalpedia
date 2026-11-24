-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GradedFrameCharacterisation_repr_of_sub_mem_5ce60ba3d5bd
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_GradedFrameCharacterisation_repr_of_sub_mem_5ce60ba3d5bd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:51.083713+00:00
-- url     : https://prove2.me/theorems/a0746f89-5009-40e9-bf99-5d3a6be5bc25
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Graded Frame Characterisation repr of sub mem 5ce60ba3d5bd: P2 M Ground Theory Heights  Heights Numbers DVR Graded Frame Characterisation repr of sub me
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Graded Frame Characterisation repr of sub mem 5ce60ba3d5bd construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Graded Frame Characterisation repr of sub mem 5ce60ba3d5bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinGradedFrameIff.lean#L56-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinGradedFrameIff.lean#L56-L74

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_GradedFrameCharacterisation_repr_of_sub_mem_5ce60ba3d5bd (w : Module.Basis (Fin N) Ω E) {x : E} {i : Fin N} {t : Ω}
    (hx : x - t • w i ∈
      Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < ((Fin.castSucc i : Fin (N + 1)) : ℕ)})) :
    (∀ j, i < j → w.repr x j = 0) ∧ w.repr x i = t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«GradedFrameCharacterisation».«repr_of_sub_mem» := P2M_GroundTheory_Heights__Heights_NumbersDVR_GradedFrameCharacterisation_repr_of_sub_mem_5ce60ba3d5bd
