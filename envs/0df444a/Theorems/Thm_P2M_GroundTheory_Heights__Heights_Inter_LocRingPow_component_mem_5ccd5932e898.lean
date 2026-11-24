-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_LocRingPow_component_mem_5ccd5932e898
-- name    : P2M_GroundTheory_Heights__Heights_Inter_LocRingPow_component_mem_5ccd5932e898
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:22:58.619643+00:00
-- url     : https://prove2.me/theorems/6d8124b4-aeef-4392-adda-4f68ba5c1397
-- title:
--   P2 M Ground Theory Heights  Heights Inter Loc Ring Pow component mem 5ccd5932e898: P2 M Ground Theory Heights  Heights Inter Loc Ring Pow component mem 5ccd5932e898
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Loc Ring Pow component mem 5ccd5932e898 construction uses the P2 M Ground Theory Heights  Heights Inter Loc Ring Pow component mem 5ccd5932e898 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PLocRingPow.lean#L41-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PLocRingPow.lean#L41-L49

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

theorem P2M_GroundTheory_Heights__Heights_Inter_LocRingPow_component_mem_5ccd5932e898 [DecidableEq K] {J : Ideal (MRing ι)} (hJ : IsMultiHomogIdeal J) {f : MRing ι}
    (hf : f ∈ J) (D : K → ℕ) : weightedHomogeneousComponent (multiDegWeight ι) D f ∈ J := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«LocRingPow».«component_mem» := P2M_GroundTheory_Heights__Heights_Inter_LocRingPow_component_mem_5ccd5932e898
