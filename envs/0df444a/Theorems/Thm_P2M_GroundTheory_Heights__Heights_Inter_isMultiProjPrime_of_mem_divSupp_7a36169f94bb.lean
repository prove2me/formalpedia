-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isMultiProjPrime_of_mem_divSupp_7a36169f94bb
-- name    : P2M_GroundTheory_Heights__Heights_Inter_isMultiProjPrime_of_mem_divSupp_7a36169f94bb
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:24:13.283704+00:00
-- url     : https://prove2.me/theorems/f6cb7c71-c92f-494b-8308-b83328ee1b61
-- title:
--   P2 M Ground Theory Heights  Heights Inter is Multi Proj Prime of mem div Supp 7a36169f94bb: P2 M Ground Theory Heights  Heights Inter is Multi Proj Prime of mem div Supp 7a36169f94bb
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter is Multi Proj Prime of mem div Supp 7a36169f94bb construction uses the P2 M Ground Theory Heights  Heights Inter is Multi Proj Prime of mem div Supp 7a36169f94bb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PWellDefined.lean#L19-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PWellDefined.lean#L19-L22

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

theorem P2M_GroundTheory_Heights__Heights_Inter_isMultiProjPrime_of_mem_divSupp_7a36169f94bb {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} (hP : IsMultiProjPrime P) {u : MRing ι} {b : K → ℕ} (hu : IsMultiHomog u b)
    {W : Ideal (MRing ι)} (hW : W ∈ divSupp P u) : IsMultiProjPrime W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«isMultiProjPrime_of_mem_divSupp» := P2M_GroundTheory_Heights__Heights_Inter_isMultiProjPrime_of_mem_divSupp_7a36169f94bb
