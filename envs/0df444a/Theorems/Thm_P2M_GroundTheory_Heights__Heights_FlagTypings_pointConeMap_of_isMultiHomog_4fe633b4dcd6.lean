-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FlagTypings_pointConeMap_of_isMultiHomog_4fe633b4dcd6
-- name    : P2M_GroundTheory_Heights__Heights_FlagTypings_pointConeMap_of_isMultiHomog_4fe633b4dcd6
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:18:20.867801+00:00
-- url     : https://prove2.me/theorems/0a17b6aa-9604-48ae-93bc-32d613462489
-- title:
--   P2 M Ground Theory Heights  Heights Flag Typings point Cone Map of is Multi Homog 4fe633b4dcd6: P2 M Ground Theory Heights  Heights Flag Typings point Cone Map of is Multi Homog 4fe633b4dcd6
-- statement:
--   The P2 M Ground Theory Heights  Heights Flag Typings point Cone Map of is Multi Homog 4fe633b4dcd6 construction uses the P2 M Ground Theory Heights  Heights Flag Typings point Cone Map of is Multi Homog 4fe633b4dcd6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsVerticalDivOfIsVerticalDivisor.lean#L21-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsVerticalDivOfIsVerticalDivisor.lean#L21-L36

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
variable {R : Type*} [CommRing R] {Ω : Type*} [Field Ω] [Algebra R Ω]

theorem P2M_GroundTheory_Heights__Heights_FlagTypings_pointConeMap_of_isMultiHomog_4fe633b4dcd6 (y : (Σ k, ι k) → Ω) {s : MRingOver R ι} {a : K → ℕ}
    (hs : IsMultiHomog s a) :
    NumbersDVR.pointConeMap R y s = C (aeval y s) * ∏ k, X k ^ a k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FlagTypings».«pointConeMap_of_isMultiHomog» := P2M_GroundTheory_Heights__Heights_FlagTypings_pointConeMap_of_isMultiHomog_4fe633b4dcd6
