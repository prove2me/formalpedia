-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FlagTypings_divCycle_eq_4ff6952c8612
-- name    : P2M_GroundTheory_Heights__Heights_FlagTypings_divCycle_eq_4ff6952c8612
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:20:40.700309+00:00
-- url     : https://prove2.me/theorems/43530d75-9097-51db-ac60-355ed0dfa084
-- title:
--   P2 M Ground Theory Heights  Heights Flag Typings div Cycle eq 4ff6952c8612: P2 M Ground Theory Heights  Heights Flag Typings div Cycle eq 4ff6952c8612
-- statement:
--   The P2 M Ground Theory Heights  Heights Flag Typings div Cycle eq 4ff6952c8612 construction uses the P2 M Ground Theory Heights  Heights Flag Typings div Cycle eq 4ff6952c8612 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsVerticalDivOfIsVerticalDivisor.lean#L191-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsVerticalDivOfIsVerticalDivisor.lean#L191-L204

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
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_FlagTypings_divCycle_eq_4ff6952c8612 {R : Type*} [CommRing R] [IsNoetherianRing R] (P : Ideal (MRingOver R ι))
    (f : MRingOver R ι) (W : Ideal (MRingOver R ι)) :
    NumbersDVR.divCycle P f W = (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f W : ℤ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FlagTypings».«divCycle_eq» := P2M_GroundTheory_Heights__Heights_FlagTypings_divCycle_eq_4ff6952c8612
