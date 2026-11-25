-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointsBilinear_finsum_mem_sum_comm_99abf742b05d
-- name    : P2M_GroundTheory_Heights__Heights_PointsBilinear_finsum_mem_sum_comm_99abf742b05d
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:15:49.001482+00:00
-- url     : https://prove2.me/theorems/9a8fc69d-2dce-43df-b71a-12da043407b5
-- title:
--   P2 M Ground Theory Heights  Heights Points Bilinear finsum mem sum comm 99abf742b05d: P2 M Ground Theory Heights  Heights Points Bilinear finsum mem sum comm 99abf742b05d
-- statement:
--   The P2 M Ground Theory Heights  Heights Points Bilinear finsum mem sum comm 99abf742b05d construction uses the P2 M Ground Theory Heights  Heights Points Bilinear finsum mem sum comm 99abf742b05d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsBilinear.lean#L118-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsBilinear.lean#L118-L121

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasChainA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsBilinear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PtsIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsBilinear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open scoped ContDiff
open GroundTheory.Heights₂.Heights.PointsBilinear
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_PointsBilinear_finsum_mem_sum_comm_99abf742b05d {α T : Type*} [Fintype T] {S : Set α} (hS : S.Finite) (F : T → α → ℝ) :
    ∑ᶠ w ∈ S, ∑ t, F t w = ∑ t, ∑ᶠ w ∈ S, F t w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PointsBilinear».«finsum_mem_sum_comm» := P2M_GroundTheory_Heights__Heights_PointsBilinear_finsum_mem_sum_comm_99abf742b05d
