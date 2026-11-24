-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FlagTypings_coe_monoList_5c30c97751a1
-- name    : P2M_GroundTheory_Heights__Heights_FlagTypings_coe_monoList_5c30c97751a1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:04:08.884065+00:00
-- url     : https://prove2.me/theorems/94feb807-9526-4d76-8eab-42b67bd9a8c4
-- title:
--   P2 M Ground Theory Heights  Heights Flag Typings coe mono List 5c30c97751a1: P2 M Ground Theory Heights  Heights Flag Typings coe mono List 5c30c97751a1
-- statement:
--   The P2 M Ground Theory Heights  Heights Flag Typings coe mono List 5c30c97751a1 construction uses the P2 M Ground Theory Heights  Heights Flag Typings coe mono List 5c30c97751a1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsVerticalDivOfIsVerticalDivisor.lean#L162-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsVerticalDivOfIsVerticalDivisor.lean#L162-L168

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

theorem P2M_GroundTheory_Heights__Heights_FlagTypings_coe_monoList_5c30c97751a1 {N : ℕ} (μ : Fin N →₀ ℕ) :
    ((IndefiniteRowSideFullHecke.NumbersDVR.monoList μ : List (Fin N)) : Multiset (Fin N)) = Finsupp.toMultiset μ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FlagTypings».«coe_monoList» := P2M_GroundTheory_Heights__Heights_FlagTypings_coe_monoList_5c30c97751a1
