-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FlagTypings_isMultiHomog_iff_8163629d7f47
-- name    : P2M_GroundTheory_Heights__Heights_FlagTypings_isMultiHomog_iff_8163629d7f47
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:02:37.189171+00:00
-- url     : https://prove2.me/theorems/349000b0-4c22-481d-8494-df869b6a5758
-- title:
--   P2 M Ground Theory Heights  Heights Flag Typings is Multi Homog iff 8163629d7f47: P2 M Ground Theory Heights  Heights Flag Typings is Multi Homog iff 8163629d7f47
-- statement:
--   The P2 M Ground Theory Heights  Heights Flag Typings is Multi Homog iff 8163629d7f47 construction uses the P2 M Ground Theory Heights  Heights Flag Typings is Multi Homog iff 8163629d7f47 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsVerticalDivOfIsVerticalDivisor.lean#L119-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsVerticalDivOfIsVerticalDivisor.lean#L119-L128

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

theorem P2M_GroundTheory_Heights__Heights_FlagTypings_isMultiHomog_iff_8163629d7f47 (f : MRingOver R ι) (a : K → ℕ) :
    NumbersDVR.IsMultiHomog f a ↔ IsMultiHomog f a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FlagTypings».«isMultiHomog_iff» := P2M_GroundTheory_Heights__Heights_FlagTypings_isMultiHomog_iff_8163629d7f47
