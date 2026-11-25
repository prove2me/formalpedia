-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairCharacterisation_mem_flag_iff_fab23907a0d5
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairCharacterisation_mem_flag_iff_fab23907a0d5
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:07:03.587577+00:00
-- url     : https://prove2.me/theorems/b890feac-54f0-4005-a216-5e5b7b901345
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Characterisation mem flag iff fab23907a0d5: P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Characterisation mem flag iff fab23907a0
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Characterisation mem flag iff fab23907a0d5 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Characterisation mem flag iff fab23907a0d5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinFlagPairIff.lean#L44-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinFlagPairIff.lean#L44-L53

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairCharacterisation_mem_flag_iff_fab23907a0d5 (w : Module.Basis (Fin N) Ω E) (n : ℕ) (x : E) :
    x ∈ Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < n}) ↔ ∀ j : Fin N, n ≤ (j : ℕ) → w.repr x j = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagPairCharacterisation».«mem_flag_iff» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairCharacterisation_mem_flag_iff_fab23907a0d5
