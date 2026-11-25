-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairCharacterisation_flag_eq_74c67895a811
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairCharacterisation_flag_eq_74c67895a811
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:06:34.121406+00:00
-- url     : https://prove2.me/theorems/566215f7-7b24-4247-afde-ba7f476c7c55
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Characterisation flag eq 74c67895a811: P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Characterisation flag eq 74c67895a811
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Characterisation flag eq 74c67895a811 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Characterisation flag eq 74c67895a811 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinFlagPairIff.lean#L30-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinFlagPairIff.lean#L30-L38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinVertDivIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinGradedFrameIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinFlagPairIff
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
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
universe u v w
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagPairCharacterisation
variable {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairCharacterisation_flag_eq_74c67895a811 (w : Module.Basis (Fin N) Ω E) {Vs : Fin (N + 1) → Submodule Ω E} (mono : Monotone Vs)
    (dim : ∀ i, Module.finrank Ω (Vs i) = (i : ℕ)) (hmem : ∀ j, w j ∈ Vs j.succ) (i : Fin (N + 1)) :
    Vs i = Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < i}) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagPairCharacterisation».«flag_eq» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairCharacterisation_flag_eq_74c67895a811
