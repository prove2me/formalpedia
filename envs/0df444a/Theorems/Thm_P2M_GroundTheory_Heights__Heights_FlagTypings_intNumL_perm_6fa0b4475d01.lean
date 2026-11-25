-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FlagTypings_intNumL_perm_6fa0b4475d01
-- name    : P2M_GroundTheory_Heights__Heights_FlagTypings_intNumL_perm_6fa0b4475d01
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:03:19.854857+00:00
-- url     : https://prove2.me/theorems/852b39e9-9d29-49b6-b061-0ed8484b6d0d
-- title:
--   P2 M Ground Theory Heights  Heights Flag Typings int Num L perm 6fa0b4475d01: P2 M Ground Theory Heights  Heights Flag Typings int Num L perm 6fa0b4475d01
-- statement:
--   The P2 M Ground Theory Heights  Heights Flag Typings int Num L perm 6fa0b4475d01 construction uses the P2 M Ground Theory Heights  Heights Flag Typings int Num L perm 6fa0b4475d01 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsVerticalDivOfIsVerticalDivisor.lean#L156-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsVerticalDivOfIsVerticalDivisor.lean#L156-L160

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

theorem P2M_GroundTheory_Heights__Heights_FlagTypings_intNumL_perm_6fa0b4475d01 (F : Type*) [Field F] (V : Ideal (MRingOver F ι)) {L₁ L₂ : List (K → ℤ)}
    (h : L₁.Perm L₂) : NumbersDVR.intNumL F V L₁ = NumbersDVR.intNumL F V L₂ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FlagTypings».«intNumL_perm» := P2M_GroundTheory_Heights__Heights_FlagTypings_intNumL_perm_6fa0b4475d01
