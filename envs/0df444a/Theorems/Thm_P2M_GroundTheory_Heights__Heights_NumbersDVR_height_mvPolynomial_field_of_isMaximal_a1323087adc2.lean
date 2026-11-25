-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_height_mvPolynomial_field_of_isMaximal_a1323087adc2
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_height_mvPolynomial_field_of_isMaximal_a1323087adc2
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:11:13.310961+00:00
-- url     : https://prove2.me/theorems/f9740f1c-ca79-4179-a78a-4542fde624bb
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR height mv Polynomial field of is Maximal a1323087adc2: P2 M Ground Theory Heights  Heights Numbers DVR height mv Polynomial field of is Maximal a1323087
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR height mv Polynomial field of is Maximal a1323087adc2 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR height mv Polynomial field of is Maximal a1323087adc2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PComponentDim.lean#L27-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PComponentDim.lean#L27-L33

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_height_mvPolynomial_field_of_isMaximal_a1323087adc2 {k : Type*} [Field k]
    (M : Ideal (MvPolynomial σ k)) (hM : M.IsMaximal) :
    (M.height : WithBot ℕ∞) = (Nat.card σ : WithBot ℕ∞) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«height_mvPolynomial_field_of_isMaximal» := P2M_GroundTheory_Heights__Heights_NumbersDVR_height_mvPolynomial_field_of_isMaximal_a1323087adc2
