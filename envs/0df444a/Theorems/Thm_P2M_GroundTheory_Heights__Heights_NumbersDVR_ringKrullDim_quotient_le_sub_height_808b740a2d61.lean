-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ringKrullDim_quotient_le_sub_height_808b740a2d61
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_ringKrullDim_quotient_le_sub_height_808b740a2d61
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:12:20.975795+00:00
-- url     : https://prove2.me/theorems/e13de015-bca7-4c61-9c67-47e10448b370
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR ring Krull Dim quotient le sub height 808b740a2d61: P2 M Ground Theory Heights  Heights Numbers DVR ring Krull Dim quotient le sub height 808b740a2d61
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR ring Krull Dim quotient le sub height 808b740a2d61 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR ring Krull Dim quotient le sub height 808b740a2d61 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PComponentDim.lean#L72-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PComponentDim.lean#L72-L89

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_ringKrullDim_quotient_le_sub_height_808b740a2d61 {A : Type*} [CommRing A] [IsNoetherianRing A]
    [FiniteRingKrullDim A] (P : Ideal A) [P.IsPrime] (N h : ℕ)
    (hmax : ∀ m : Ideal A, m.IsMaximal → m.height ≤ N) (hP : P.height = h) :
    ringKrullDim (A ⧸ P) ≤ ((N - h : ℕ) : WithBot ℕ∞) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«ringKrullDim_quotient_le_sub_height» := P2M_GroundTheory_Heights__Heights_NumbersDVR_ringKrullDim_quotient_le_sub_height_808b740a2d61
