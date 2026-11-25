-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FlagTypings_vNumL_perm_1d903d9128b0
-- name    : P2M_GroundTheory_Heights__Heights_FlagTypings_vNumL_perm_1d903d9128b0
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:16:59.505276+00:00
-- url     : https://prove2.me/theorems/810937ab-5079-5eb1-9f45-267538c77c2c
-- title:
--   P2 M Ground Theory Heights  Heights Flag Typings v Num L perm 1d903d9128b0: P2 M Ground Theory Heights  Heights Flag Typings v Num L perm 1d903d9128b0
-- statement:
--   The P2 M Ground Theory Heights  Heights Flag Typings v Num L perm 1d903d9128b0 construction uses the P2 M Ground Theory Heights  Heights Flag Typings v Num L perm 1d903d9128b0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsVerticalDivOfIsVerticalDivisor.lean#L249-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsVerticalDivOfIsVerticalDivisor.lean#L249-L251

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
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {N : ℕ}
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_FlagTypings_vNumL_perm_1d903d9128b0 (W : Ideal (MRingOver O ι)) {L₁ L₂ : List (K → ℤ)} (h : L₁.Perm L₂) :
    NumbersDVR.vNumL W L₁ = NumbersDVR.vNumL W L₂ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FlagTypings».«vNumL_perm» := P2M_GroundTheory_Heights__Heights_FlagTypings_vNumL_perm_1d903d9128b0
