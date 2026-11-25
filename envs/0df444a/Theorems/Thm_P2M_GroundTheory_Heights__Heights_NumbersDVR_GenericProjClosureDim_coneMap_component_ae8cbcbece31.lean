-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDim_coneMap_component_ae8cbcbece31
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDim_coneMap_component_ae8cbcbece31
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:08:55.749777+00:00
-- url     : https://prove2.me/theorems/faa95283-c574-471a-be74-075dfe866169
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Dim cone Map component ae8cbcbece31: P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Dim cone Map component ae
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Dim cone Map component ae8cbcbece31 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Dim cone Map component ae8cbcbece31 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericProjClosureDim.lean#L21-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericProjClosureDim.lean#L21-L39

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDim_coneMap_component_ae8cbcbece31 (z : (Σ k, ι k) → L) (b : K → ℕ) (f : MRing ι R) :
    weightedHomogeneousComponent (tWeight K) b (pointConeMap R z f) =
      pointConeMap R z (weightedHomogeneousComponent (blockWeight ι) b f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«GenericProjClosureDim».«coneMap_component» := P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDim_coneMap_component_ae8cbcbece31
