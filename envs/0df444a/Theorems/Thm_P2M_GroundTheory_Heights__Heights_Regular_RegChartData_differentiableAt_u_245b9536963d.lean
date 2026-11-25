-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RegChartData_differentiableAt_u_245b9536963d
-- name    : P2M_GroundTheory_Heights__Heights_Regular_RegChartData_differentiableAt_u_245b9536963d
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:35:30.848811+00:00
-- url     : https://prove2.me/theorems/a92951bf-e9af-5f48-9dcf-fe4d46c6e43e
-- title:
--   P2 M Ground Theory Heights  Heights Regular Reg Chart Data differentiable At u 245b9536963d: P2 M Ground Theory Heights  Heights Regular Reg Chart Data differentiable At u 245b9536963d
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Reg Chart Data differentiable At u 245b9536963d construction uses the P2 M Ground Theory Heights  Heights Regular Reg Chart Data differentiable At u 245b9536963d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PMollifiedNearSmooth.lean#L40-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PMollifiedNearSmooth.lean#L40-L47

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

theorem P2M_GroundTheory_Heights__Heights_Regular_RegChartData_differentiableAt_u_245b9536963d (j : Fin R.N) {y : Fin D → ℂ} (hy : y ∈ (R.chart j).target)
    (hyA : y ∉ coordDiv (R.S j)) : DifferentiableAt ℝ (R.u j) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«RegChartData».«differentiableAt_u» := P2M_GroundTheory_Heights__Heights_Regular_RegChartData_differentiableAt_u_245b9536963d
