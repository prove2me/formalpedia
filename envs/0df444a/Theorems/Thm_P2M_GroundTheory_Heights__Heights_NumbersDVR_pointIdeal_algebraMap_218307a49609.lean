-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_pointIdeal_algebraMap_218307a49609
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_pointIdeal_algebraMap_218307a49609
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:02.224922+00:00
-- url     : https://prove2.me/theorems/d8807596-bb66-4563-8030-4af6c64a46ec
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR point Ideal algebra Map 218307a49609: P2 M Ground Theory Heights  Heights Numbers DVR point Ideal algebra Map 218307a49609
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR point Ideal algebra Map 218307a49609 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR point Ideal algebra Map 218307a49609 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSegreFlagClosurePullback.lean#L138-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSegreFlagClosurePullback.lean#L138-L156

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagClosure
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagIndependence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairNumberRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsVerticalDivisorJoinPullback
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagClosureBirational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagClosurePullback
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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_pointIdeal_algebraMap_218307a49609 {K : Type*} {ι : K → Type*} {O Ω Φ : Type*} [CommRing O] [Field Ω] [Field Φ]
    [Algebra O Ω] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ] (y : (Σ k, ι k) → Ω) :
    pointIdeal O (fun p => algebraMap Ω Φ (y p)) = pointIdeal O y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«pointIdeal_algebraMap» := P2M_GroundTheory_Heights__Heights_NumbersDVR_pointIdeal_algebraMap_218307a49609
