-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isVerticalDivisor_one_177da7b5f629
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_isVerticalDivisor_one_177da7b5f629
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:37:22.920825+00:00
-- url     : https://prove2.me/theorems/dfda3c9b-5ef8-4979-9180-cc53dce117ca
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR is Vertical Divisor one 177da7b5f629: P2 M Ground Theory Heights  Heights Numbers DVR is Vertical Divisor one 177da7b5f629
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR is Vertical Divisor one 177da7b5f629 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR is Vertical Divisor one 177da7b5f629 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsBundles.lean#L139-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsBundles.lean#L139-L154

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles
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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_isVerticalDivisor_one_177da7b5f629 {K : Type*} [DecidableEq K] {ι : K → Type*} {O : Type*} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (H : Ideal (MRing ι O)) [H.IsPrime] :
    IsVerticalDivisor H ϖ 0 1 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«isVerticalDivisor_one» := P2M_GroundTheory_Heights__Heights_NumbersDVR_isVerticalDivisor_one_177da7b5f629
