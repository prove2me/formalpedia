-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinRight_chartMon_mid_dac97e5de086
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinRight_chartMon_mid_dac97e5de086
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:38:04.987894+00:00
-- url     : https://prove2.me/theorems/a456ded3-a200-5c3c-b6e0-c364c13cdc7b
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Join Right chart Mon mid dac97e5de086: P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Join Right chart Mon mid dac97e5de086
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Join Right chart Mon mid dac97e5de086 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Join Right chart Mon mid dac97e5de086 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinFlagPairJoinRight.lean#L53-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinFlagPairJoinRight.lean#L53-L58

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinRight_chartMon_mid_dac97e5de086 (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (w : (Σ k, ι₂ k) → Ω)
    (s : ∀ k : K ⊕ (K₂ ⊕ K'), Sum.elim ι (Sum.elim ι₂ ι') k) (a : K ⊕ K' → ℤ) :
    chartMon (joinCoord x (joinCoord w z)) s (midDeg (K₂ := K₂) a) =
      chartMon (joinCoord x z) (midChart s) a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagPairJoinRight».«chartMon_mid» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinRight_chartMon_mid_dac97e5de086
