-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairCharacterisation_linearIndependent_of_not_mem_98e9524d2579
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairCharacterisation_linearIndependent_of_not_mem_98e9524d2579
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:12:48.189972+00:00
-- url     : https://prove2.me/theorems/c46c7056-02c3-5b55-a74f-1d71bf1cb787
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Characterisation linear Independent of not mem 98e9524d2579: P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Characterisation linear
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Characterisation linear Independent of not mem 98e9524d2579 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Characterisation linear Independent of not mem 98e9524d2579 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinFlagPairIff.lean#L55-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinFlagPairIff.lean#L55-L85

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairCharacterisation_linearIndependent_of_not_mem_98e9524d2579 {Vs : Fin (N + 1) → Submodule Ω E} (mono : Monotone Vs)
    {gen : Fin N → E} (hmem : ∀ i, gen i ∈ Vs i.succ) (hnot : ∀ i, gen i ∉ Vs i.castSucc) :
    LinearIndependent Ω gen := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagPairCharacterisation».«linearIndependent_of_not_mem» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairCharacterisation_linearIndependent_of_not_mem_98e9524d2579
