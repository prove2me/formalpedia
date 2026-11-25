-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_le_height_of_isMaximal_of_uniformiser_mem_3234f83b7778
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_le_height_of_isMaximal_of_uniformiser_mem_3234f83b7778
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:11:27.267794+00:00
-- url     : https://prove2.me/theorems/56b0b8ab-631e-48ab-896a-2be64f626e15
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR le height of is Maximal of uniformiser mem 3234f83b7778: P2 M Ground Theory Heights  Heights Numbers DVR le height of is Maximal of uniformiser mem 3234
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR le height of is Maximal of uniformiser mem 3234f83b7778 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR le height of is Maximal of uniformiser mem 3234f83b7778 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PComponentDim.lean#L35-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PComponentDim.lean#L35-L70

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsComponentDim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAB
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_WithBotEqOfLeOfAddOneLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PComponentDim
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
universe u
variable {σ : Type*} [Finite σ]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_le_height_of_isMaximal_of_uniformiser_mem_3234f83b7778 {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ) (m : Ideal (MvPolynomial σ O))
    (hm : m.IsMaximal) (hϖm : (C ϖ : MvPolynomial σ O) ∈ m) :
    ((Nat.card σ + 1 : ℕ) : ℕ∞) ≤ m.height := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«le_height_of_isMaximal_of_uniformiser_mem» := P2M_GroundTheory_Heights__Heights_NumbersDVR_le_height_of_isMaximal_of_uniformiser_mem_3234f83b7778
