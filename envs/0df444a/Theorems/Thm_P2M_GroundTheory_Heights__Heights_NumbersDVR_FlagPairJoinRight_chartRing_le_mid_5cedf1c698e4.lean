-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinRight_chartRing_le_mid_5cedf1c698e4
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinRight_chartRing_le_mid_5cedf1c698e4
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:34:23.849983+00:00
-- url     : https://prove2.me/theorems/1c89853c-8d07-554a-8b08-106cf83535b5
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Join Right chart Ring le mid 5cedf1c698e4: P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Join Right chart Ring le mid 5cedf1c698e4
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Join Right chart Ring le mid 5cedf1c698e4 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Join Right chart Ring le mid 5cedf1c698e4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinFlagPairJoinRight.lean#L62-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinFlagPairJoinRight.lean#L62-L79

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
variable (O : Type*) [CommRing O] [Algebra O Ω]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinRight_chartRing_le_mid_5cedf1c698e4 (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (w : (Σ k, ι₂ k) → Ω)
    (s : ∀ k : K ⊕ (K₂ ⊕ K'), Sum.elim ι (Sum.elim ι₂ ι') k)
    (hs : mseg (joinCoord x (joinCoord w z)) s ≠ 0) :
    chartRing O (mseg (joinCoord x z)) (midChart s) ≤ chartRing O (mseg (joinCoord x (joinCoord w z))) s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagPairJoinRight».«chartRing_le_mid» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinRight_chartRing_le_mid_5cedf1c698e4
