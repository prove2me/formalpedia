-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FlagTypings_weight_blockWeight_8aa7cbb3c809
-- name    : P2M_GroundTheory_Heights__Heights_FlagTypings_weight_blockWeight_8aa7cbb3c809
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:20:46.595055+00:00
-- url     : https://prove2.me/theorems/b7c0b358-9bec-5235-a816-33201ddde5d5
-- title:
--   P2 M Ground Theory Heights  Heights Flag Typings weight block Weight 8aa7cbb3c809: P2 M Ground Theory Heights  Heights Flag Typings weight block Weight 8aa7cbb3c809
-- statement:
--   The P2 M Ground Theory Heights  Heights Flag Typings weight block Weight 8aa7cbb3c809 construction uses the P2 M Ground Theory Heights  Heights Flag Typings weight block Weight 8aa7cbb3c809 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsVerticalDivOfIsVerticalDivisor.lean#L112-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsVerticalDivOfIsVerticalDivisor.lean#L112-L117

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_TrivBundleIsTwistedForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisor
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FlagTypings
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
set_option linter.unusedSectionVars false
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_FlagTypings_weight_blockWeight_8aa7cbb3c809 (d : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (NumbersDVR.blockWeight ι) d k = ∑ i, d ⟨k, i⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FlagTypings».«weight_blockWeight» := P2M_GroundTheory_Heights__Heights_FlagTypings_weight_blockWeight_8aa7cbb3c809
