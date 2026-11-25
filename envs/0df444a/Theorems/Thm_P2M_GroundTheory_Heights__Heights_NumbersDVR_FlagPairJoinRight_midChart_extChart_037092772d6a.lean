-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinRight_midChart_extChart_037092772d6a
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinRight_midChart_extChart_037092772d6a
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:31:30.550604+00:00
-- url     : https://prove2.me/theorems/4aa52ce0-4cd1-407d-b2fc-df66db841ea6
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Join Right mid Chart ext Chart 037092772d6a: P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Join Right mid Chart ext Chart 03709277
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Join Right mid Chart ext Chart 037092772d6a construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Join Right mid Chart ext Chart 037092772d6a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinFlagPairJoinRight.lean#L37-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinFlagPairJoinRight.lean#L37-L40

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
variable {Ω : Type*} [Field Ω] {K K' K₂ : Type} [Fintype K] [Fintype K'] [Fintype K₂]
  {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinRight_midChart_extChart_037092772d6a (t : ∀ k : K ⊕ K', Sum.elim ι ι' k) (u : ∀ k, ι₂ k) :
    midChart (extChart t u) = t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagPairJoinRight».«midChart_extChart» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinRight_midChart_extChart_037092772d6a
