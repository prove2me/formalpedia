-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_LocRingPow_component_mul_of_not_le_458ee4a08c44
-- name    : P2M_GroundTheory_Heights__Heights_Inter_LocRingPow_component_mul_of_not_le_458ee4a08c44
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:41:52.719297+00:00
-- url     : https://prove2.me/theorems/eb6a391b-c836-4eb8-8ed0-0f629d58be83
-- title:
--   P2 M Ground Theory Heights  Heights Inter Loc Ring Pow component mul of not le 458ee4a08c44: P2 M Ground Theory Heights  Heights Inter Loc Ring Pow component mul of not le 458ee4a08c44
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Loc Ring Pow component mul of not le 458ee4a08c44 construction uses the P2 M Ground Theory Heights  Heights Inter Loc Ring Pow component mul of not le 458ee4a08c44 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PLocRingPow.lean#L76-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PLocRingPow.lean#L76-L81

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StLocRingPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.Inter.AvoidRing
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.LocRingPow
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
omit [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_LocRingPow_component_mul_of_not_le_458ee4a08c44 [DecidableEq K] {f g : MRing ι} {j n : K → ℕ}
    (hg : IsWeightedHomogeneous (multiDegWeight ι) g j) (h : ¬ j ≤ n) :
    weightedHomogeneousComponent (multiDegWeight ι) n (f * g) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«LocRingPow».«component_mul_of_not_le» := P2M_GroundTheory_Heights__Heights_Inter_LocRingPow_component_mul_of_not_le_458ee4a08c44
