-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinRight_midDeg_sub_4ada2875cf88
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinRight_midDeg_sub_4ada2875cf88
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:34:03.438815+00:00
-- url     : https://prove2.me/theorems/4f13b193-c451-52d8-83de-5a1c2f01058a
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Join Right mid Deg sub 4ada2875cf88: P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Join Right mid Deg sub 4ada2875cf88
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Join Right mid Deg sub 4ada2875cf88 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Join Right mid Deg sub 4ada2875cf88 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinFlagPairJoinRight.lean#L94-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinFlagPairJoinRight.lean#L94-L97

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsMoreAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinFlagPairJoinRight
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_Bundles_joinCoord_midVar_3ed08dc9bce4

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing div_mem_chartRing)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg joinCoord restrictChart chartMon IsGradedFrame IsUnitOn FlagPair IsPull
  midDeg midVar joinCoord_midVar)
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagPairJoinRight
variable {O : Type*} [CommRing O] {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K K' K₂ : Type} {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinRight_midDeg_sub_4ada2875cf88 (a b : K ⊕ K' → ℤ) :
    midDeg (K₂ := K₂) a - midDeg (K₂ := K₂) b = midDeg (K₂ := K₂) (a - b) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagPairJoinRight».«midDeg_sub» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinRight_midDeg_sub_4ada2875cf88
