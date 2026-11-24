-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDim_isMultiProjPrime_pointIdeal_058978c6cf77
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDim_isMultiProjPrime_pointIdeal_058978c6cf77
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:21.118219+00:00
-- url     : https://prove2.me/theorems/1ef008c3-a3e4-4cb7-bd92-46e2d7d149b0
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Dim is Multi Proj Prime point Ideal 058978c6cf77: P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Dim is Multi
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Dim is Multi Proj Prime point Ideal 058978c6cf77 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Dim is Multi Proj Prime point Ideal 058978c6cf77 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericProjClosureDim.lean#L41-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericProjClosureDim.lean#L41-L55

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsGenericProjClosureDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsDvrConeDimTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairBundleTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwistedDualGensSpan
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericProjClosureDim
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDim
variable {R : Type*} [CommRing R] {L : Type*} [Field L] [Algebra R L] {K : Type*} [DecidableEq K]
  {ι : K → Type*}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDim_isMultiProjPrime_pointIdeal_058978c6cf77 (z : (Σ k, ι k) → L) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    IsMultiProjPrime (pointIdeal R z) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«GenericProjClosureDim».«isMultiProjPrime_pointIdeal» := P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDim_isMultiProjPrime_pointIdeal_058978c6cf77
