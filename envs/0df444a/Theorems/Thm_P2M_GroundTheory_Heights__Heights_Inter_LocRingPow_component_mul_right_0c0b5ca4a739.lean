-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_LocRingPow_component_mul_right_0c0b5ca4a739
-- name    : P2M_GroundTheory_Heights__Heights_Inter_LocRingPow_component_mul_right_0c0b5ca4a739
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:41:33.713923+00:00
-- url     : https://prove2.me/theorems/4732d247-6883-4e3a-ac37-12e06c273af5
-- title:
--   P2 M Ground Theory Heights  Heights Inter Loc Ring Pow component mul right 0c0b5ca4a739: P2 M Ground Theory Heights  Heights Inter Loc Ring Pow component mul right 0c0b5ca4a739
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Loc Ring Pow component mul right 0c0b5ca4a739 construction uses the P2 M Ground Theory Heights  Heights Inter Loc Ring Pow component mul right 0c0b5ca4a739 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PLocRingPow.lean#L66-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PLocRingPow.lean#L66-L72

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

theorem P2M_GroundTheory_Heights__Heights_Inter_LocRingPow_component_mul_right_0c0b5ca4a739 [DecidableEq K] {f g : MRing ι} {i j : K → ℕ}
    (hg : IsWeightedHomogeneous (multiDegWeight ι) g j) :
    weightedHomogeneousComponent (multiDegWeight ι) (i + j) (f * g) =
      weightedHomogeneousComponent (multiDegWeight ι) i f * g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«LocRingPow».«component_mul_right» := P2M_GroundTheory_Heights__Heights_Inter_LocRingPow_component_mul_right_0c0b5ca4a739
