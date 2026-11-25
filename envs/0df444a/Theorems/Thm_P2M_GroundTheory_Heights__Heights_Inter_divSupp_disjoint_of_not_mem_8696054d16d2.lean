-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_divSupp_disjoint_of_not_mem_8696054d16d2
-- name    : P2M_GroundTheory_Heights__Heights_Inter_divSupp_disjoint_of_not_mem_8696054d16d2
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:25:25.537376+00:00
-- url     : https://prove2.me/theorems/2334f907-0958-4b41-a54a-a617e03fbd30
-- title:
--   P2 M Ground Theory Heights  Heights Inter div Supp disjoint of not mem 8696054d16d2: P2 M Ground Theory Heights  Heights Inter div Supp disjoint of not mem 8696054d16d2
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter div Supp disjoint of not mem 8696054d16d2 construction uses the P2 M Ground Theory Heights  Heights Inter div Supp disjoint of not mem 8696054d16d2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PWellDefined.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PWellDefined.lean#L14-L17

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsWellDefined
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PWellDefined
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Inter_divSupp_disjoint_of_not_mem_8696054d16d2 {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {u a : MRing ι} (h : ∀ W ∈ divSupp P u, a ∉ W) :
    ∀ W, W ∈ divSupp P u → W ∉ divSupp P a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«divSupp_disjoint_of_not_mem» := P2M_GroundTheory_Heights__Heights_Inter_divSupp_disjoint_of_not_mem_8696054d16d2
