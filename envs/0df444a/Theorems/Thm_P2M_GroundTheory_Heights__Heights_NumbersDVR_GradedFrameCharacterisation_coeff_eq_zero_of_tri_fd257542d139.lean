-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GradedFrameCharacterisation_coeff_eq_zero_of_tri_fd257542d139
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_GradedFrameCharacterisation_coeff_eq_zero_of_tri_fd257542d139
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:43.732165+00:00
-- url     : https://prove2.me/theorems/5b68c401-292f-4dd2-817d-e840b4d4be7a
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Graded Frame Characterisation coeff eq zero of tri fd257542d139: P2 M Ground Theory Heights  Heights Numbers DVR Graded Frame Characterisation coeff eq
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Graded Frame Characterisation coeff eq zero of tri fd257542d139 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Graded Frame Characterisation coeff eq zero of tri fd257542d139 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinGradedFrameIff.lean#L24-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinGradedFrameIff.lean#L24-L54

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_GradedFrameCharacterisation_coeff_eq_zero_of_tri_fd257542d139 (w : Module.Basis (Fin N) Ω E) (bb : Fin N → E)
    (hup : ∀ q j : Fin N, q < j → w.repr (bb q) j = 0) (hd : ∀ q, w.repr (bb q) q ≠ 0)
    (a : Fin N → Ω) (n : ℕ) (h : ∀ j : Fin N, n ≤ (j : ℕ) → w.repr (∑ q, a q • bb q) j = 0) :
    ∀ q : Fin N, n ≤ (q : ℕ) → a q = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«GradedFrameCharacterisation».«coeff_eq_zero_of_tri» := P2M_GroundTheory_Heights__Heights_NumbersDVR_GradedFrameCharacterisation_coeff_eq_zero_of_tri_fd257542d139
