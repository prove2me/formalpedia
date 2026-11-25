-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FlagTypings_diffStep_comm_d1aba4edb141
-- name    : P2M_GroundTheory_Heights__Heights_FlagTypings_diffStep_comm_d1aba4edb141
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:17:32.23574+00:00
-- url     : https://prove2.me/theorems/8a9d807e-59ce-4023-b3aa-8490eb7f794d
-- title:
--   P2 M Ground Theory Heights  Heights Flag Typings diff Step comm d1aba4edb141: P2 M Ground Theory Heights  Heights Flag Typings diff Step comm d1aba4edb141
-- statement:
--   The P2 M Ground Theory Heights  Heights Flag Typings diff Step comm d1aba4edb141 construction uses the P2 M Ground Theory Heights  Heights Flag Typings diff Step comm d1aba4edb141 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsVerticalDivOfIsVerticalDivisor.lean#L146-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsVerticalDivOfIsVerticalDivisor.lean#L146-L152

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
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_FlagTypings_diffStep_comm_d1aba4edb141 (a b : K → ℤ) (h : (K → ℤ) → ℤ) :
    NumbersDVR.diffStep a (NumbersDVR.diffStep b h) =
      NumbersDVR.diffStep b (NumbersDVR.diffStep a h) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FlagTypings».«diffStep_comm» := P2M_GroundTheory_Heights__Heights_FlagTypings_diffStep_comm_d1aba4edb141
