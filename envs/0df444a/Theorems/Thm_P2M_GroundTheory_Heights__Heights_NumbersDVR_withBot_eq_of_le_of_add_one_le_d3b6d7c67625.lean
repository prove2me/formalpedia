-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_withBot_eq_of_le_of_add_one_le_d3b6d7c67625
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_withBot_eq_of_le_of_add_one_le_d3b6d7c67625
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:13:35.318003+00:00
-- url     : https://prove2.me/theorems/451b9c37-1720-479a-b1f0-7ad3694a788f
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR with Bot eq of le of add one le d3b6d7c67625: P2 M Ground Theory Heights  Heights Numbers DVR with Bot eq of le of add one le d3b6d7c67625
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR with Bot eq of le of add one le d3b6d7c67625 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR with Bot eq of le of add one le d3b6d7c67625 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PComponentDim.lean#L91-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PComponentDim.lean#L91-L93

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsComponentDim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAB
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_WithBotEqOfLeOfAddOneLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PComponentDim
import Theorems.Thm_UpperTheory_Reformulated_B_Ydd3_withBot_eq_of_le_of_add_one_le

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_withBot_eq_of_le_of_add_one_le_d3b6d7c67625 {x : WithBot ℕ∞} {c : ℕ} (h1 : (c : WithBot ℕ∞) ≤ x)
    (h2 : x + 1 ≤ ((c + 1 : ℕ) : WithBot ℕ∞)) : x = c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«withBot_eq_of_le_of_add_one_le» := P2M_GroundTheory_Heights__Heights_NumbersDVR_withBot_eq_of_le_of_add_one_le_d3b6d7c67625
