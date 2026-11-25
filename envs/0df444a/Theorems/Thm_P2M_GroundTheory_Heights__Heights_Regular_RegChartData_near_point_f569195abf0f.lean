-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RegChartData_near_point_f569195abf0f
-- name    : P2M_GroundTheory_Heights__Heights_Regular_RegChartData_near_point_f569195abf0f
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:31:47.765231+00:00
-- url     : https://prove2.me/theorems/17a3ff65-916f-478d-b973-25a2f5d36c0a
-- title:
--   P2 M Ground Theory Heights  Heights Regular Reg Chart Data near point f569195abf0f: P2 M Ground Theory Heights  Heights Regular Reg Chart Data near point f569195abf0f
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Reg Chart Data near point f569195abf0f construction uses the P2 M Ground Theory Heights  Heights Regular Reg Chart Data near point f569195abf0f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PMollifiedNearSmooth.lean#L49-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PMollifiedNearSmooth.lean#L49-L130

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StatementsTruncPsh
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_GlueCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PChartComparison
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PMollifiedNearSmooth
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_polyMax_le__638c0d78514a
import Theorems.Thm_ReciprocityTheory_AnForm_A_mollify_thm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric
open scoped ContDiff
open ReciprocityTheory.AnForm.A (polyMax molli mollify_thm polyMax_le' coordDiv limsupExt)
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.RegChartData
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : ReciprocityTheory.AnForm.M.FinHolAtlas D X}
  (R : RegChartData A)

theorem P2M_GroundTheory_Heights__Heights_Regular_RegChartData_near_point_f569195abf0f {t B : ℝ} (ht : 0 < t) (hB : ∀ j, ∀ y ∈ (R.chart j).target, |R.f j y| ≤ B)
    (htB : t ≤ Real.exp (-B) / 4) {j : Fin R.N} {x : X} (hx : x ∈ R.mid j) (hxY : x ∈ R.Yo)
    (hr : R.r x ≤ Real.log t⁻¹) {y : Fin D → ℂ} (hy : y ∈ closedBall (R.chart j x) t)
    (hyT : y ∈ (R.chart j).target) :
    y ∉ coordDiv (R.S j) ∧
      R.r ((R.chart j).symm y) ≤ Real.log t⁻¹ + (2 * B + D * Real.log 4) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«RegChartData».«near_point» := P2M_GroundTheory_Heights__Heights_Regular_RegChartData_near_point_f569195abf0f
