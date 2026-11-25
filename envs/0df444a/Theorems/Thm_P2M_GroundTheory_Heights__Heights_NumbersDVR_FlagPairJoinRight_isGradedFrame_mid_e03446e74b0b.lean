-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinRight_isGradedFrame_mid_e03446e74b0b
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinRight_isGradedFrame_mid_e03446e74b0b
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:32:29.624692+00:00
-- url     : https://prove2.me/theorems/eff86018-5bd9-545b-8910-cfbdc0fa4e53
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Join Right is Graded Frame mid e03446e74b0b: P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Join Right is Graded Frame mid e03446e7
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Join Right is Graded Frame mid e03446e74b0b construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Join Right is Graded Frame mid e03446e74b0b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinFlagPairJoinRight.lean#L122-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinFlagPairJoinRight.lean#L122-L228

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
variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K K' K₂ : Type} [Fintype K] [Fintype K'] [Fintype K₂] {ι : K → Type} {ι' : K' → Type}
  {ι₂ : K₂ → Type} [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] [∀ k, Fintype (ι₂ k)]
variable {N : ℕ} {V : Type*} [AddCommGroup V] [Module Ω V]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinRight_isGradedFrame_mid_e03446e74b0b (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (w : (Σ k, ι₂ k) → Ω)
    {E : ChartBundle O (mseg x) N V} {EF : ChartBundle O (mseg (joinCoord x z)) N V}
    {EB : ChartBundle O (mseg (joinCoord x (joinCoord w z))) N V} (hF : IsPull O x z E EF)
    (hB : IsPull O x (joinCoord w z) E EB) {Vs : Fin (N + 1) → Submodule Ω V} {m : Fin N → K ⊕ K' → ℤ}
    {gen : Fin N → V} (h : IsGradedFrame O (joinCoord x z) EF Vs m gen) :
    IsGradedFrame O (joinCoord x (joinCoord w z)) EB Vs (fun i => midDeg (K₂ := K₂) (m i)) gen := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagPairJoinRight».«isGradedFrame_mid» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinRight_isGradedFrame_mid_e03446e74b0b
