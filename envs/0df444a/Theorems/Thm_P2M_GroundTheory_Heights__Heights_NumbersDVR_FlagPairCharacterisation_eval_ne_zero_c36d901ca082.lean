-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairCharacterisation_eval_ne_zero_c36d901ca082
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairCharacterisation_eval_ne_zero_c36d901ca082
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:05:59.34945+00:00
-- url     : https://prove2.me/theorems/d2a11c19-5728-4505-8b34-d4f4de1fa588
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Characterisation eval ne zero c36d901ca082: P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Characterisation eval ne zero c36d901ca0
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Characterisation eval ne zero c36d901ca082 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Pair Characterisation eval ne zero c36d901ca082 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinFlagPairIff.lean#L135-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinFlagPairIff.lean#L135-L142

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
variable {o : Type*} [CommRing o] {Ω : Type*} [Field Ω] [Algebra o Ω] {K : Type} [Fintype K]
  {ι : K → Type} [∀ k, Fintype (ι k)] {y : (Σ k, ι k) → Ω} {N : ℕ} {E : Type*}
  [AddCommGroup E] [Module Ω E] {B : ChartBundle o (segreVec y) N E}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairCharacterisation_eval_ne_zero_c36d901ca082 {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω]
    [DecidableEq K] {b : K → ℤ} {f g : MRing ι O}
    (h : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O (pointIdeal O y) b f g) : aeval y g ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagPairCharacterisation».«eval_ne_zero» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairCharacterisation_eval_ne_zero_c36d901ca082
