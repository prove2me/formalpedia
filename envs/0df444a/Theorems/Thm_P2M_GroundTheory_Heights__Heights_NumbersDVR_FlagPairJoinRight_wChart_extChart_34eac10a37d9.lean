-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinRight_wChart_extChart_34eac10a37d9
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinRight_wChart_extChart_34eac10a37d9
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:37:59.727958+00:00
-- url     : https://prove2.me/theorems/fa6c7f4e-03a6-5552-a554-9bf8b7f3376c
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Join Right w Chart ext Chart 34eac10a37d9: P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Join Right w Chart ext Chart 34eac10a37d9
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Join Right w Chart ext Chart 34eac10a37d9 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Join Right w Chart ext Chart 34eac10a37d9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinFlagPairJoinRight.lean#L42-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinFlagPairJoinRight.lean#L42-L44

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinRight_wChart_extChart_34eac10a37d9 (t : ∀ k : K ⊕ K', Sum.elim ι ι' k) (u : ∀ k, ι₂ k) :
    wChart (extChart (ι₂ := ι₂) t u) = u := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagPairJoinRight».«wChart_extChart» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinRight_wChart_extChart_34eac10a37d9
