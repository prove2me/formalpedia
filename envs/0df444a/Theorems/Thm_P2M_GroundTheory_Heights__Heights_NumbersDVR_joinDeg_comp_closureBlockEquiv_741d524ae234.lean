-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_joinDeg_comp_closureBlockEquiv_741d524ae234
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_joinDeg_comp_closureBlockEquiv_741d524ae234
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:37:48.840127+00:00
-- url     : https://prove2.me/theorems/06b10503-4b8a-4a8c-bc9f-3ebb0f30ed69
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR join Deg comp closure Block Equiv 741d524ae234: P2 M Ground Theory Heights  Heights Numbers DVR join Deg comp closure Block Equiv 741d524ae234
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR join Deg comp closure Block Equiv 741d524ae234 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR join Deg comp closure Block Equiv 741d524ae234 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSegreFlagClosurePullback.lean#L51-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSegreFlagClosurePullback.lean#L51-L54

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
variable (K : Type*)
variable {K} (ι : K → Type) (M M' : ℕ)

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_joinDeg_comp_closureBlockEquiv_741d524ae234 (L : K → ℤ) :
    joinDeg (K' := Option Unit) L ∘ closureBlockEquiv K = liftPairDeg L := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«joinDeg_comp_closureBlockEquiv» := P2M_GroundTheory_Heights__Heights_NumbersDVR_joinDeg_comp_closureBlockEquiv_741d524ae234
