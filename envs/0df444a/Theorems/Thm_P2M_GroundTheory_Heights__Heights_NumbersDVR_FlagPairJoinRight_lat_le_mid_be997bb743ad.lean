-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinRight_lat_le_mid_be997bb743ad
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinRight_lat_le_mid_be997bb743ad
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:31:37.05421+00:00
-- url     : https://prove2.me/theorems/d8b37fd6-e013-4217-a899-a407dcb3656b
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Join Right lat le mid be997bb743ad: P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Join Right lat le mid be997bb743ad
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Join Right lat le mid be997bb743ad construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Join Right lat le mid be997bb743ad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinFlagPairJoinRight.lean#L108-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinFlagPairJoinRight.lean#L108-L120

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinRight_lat_le_mid_be997bb743ad (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (w : (Σ k, ι₂ k) → Ω)
    {E : ChartBundle O (mseg x) N V} {EF : ChartBundle O (mseg (joinCoord x z)) N V}
    {EB : ChartBundle O (mseg (joinCoord x (joinCoord w z))) N V} (hF : IsPull O x z E EF)
    (hB : IsPull O x (joinCoord w z) E EB) (s : ∀ k : K ⊕ (K₂ ⊕ K'), Sum.elim ι (Sum.elim ι₂ ι') k)
    (hs : mseg (joinCoord x (joinCoord w z)) s ≠ 0) :
    EF.lat (midChart s) ≤ EB.lat s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagPairJoinRight».«lat_le_mid» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinRight_lat_le_mid_be997bb743ad
