-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RegChartData_smoothed_local_a8630248a862
-- name    : P2M_GroundTheory_Heights__Heights_Regular_RegChartData_smoothed_local_a8630248a862
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:45:51.176329+00:00
-- url     : https://prove2.me/theorems/4b16922c-80c5-4a28-8bac-b5a139b4aae1
-- title:
--   P2 M Ground Theory Heights  Heights Regular Reg Chart Data smoothed local a8630248a862: P2 M Ground Theory Heights  Heights Regular Reg Chart Data smoothed local a8630248a862
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Reg Chart Data smoothed local a8630248a862 construction uses the P2 M Ground Theory Heights  Heights Regular Reg Chart Data smoothed local a8630248a862 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/GlueCharts.lean#L128-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/GlueCharts.lean#L128-L181

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_GlueCharts
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
open Metric Filter Topology Set
open scoped ContDiff
open ReciprocityTheory.AnForm.A (IsPsh Mollifier molli coordDiv limsupExt shrink)
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
open ReciprocityTheory.AnForm (levi)
noncomputable section
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}
open GroundTheory.Heights₂.Heights.Regular.RegChartData
variable (R : RegChartData A)

theorem P2M_GroundTheory_Heights__Heights_Regular_RegChartData_smoothed_local_a8630248a862 (ρ : Mollifier D) (K : ℝ) {t : ℝ} (ht : 0 < t) (j : Fin R.N)
    {z : Fin D → ℂ} (hz : closedBall z t ⊆ (R.chart j).target) :
    ContDiffAt ℝ ∞ (R.smoothed ρ K t j) z ∧ ∀ w, 0 ≤ levi (R.smoothed ρ K t j) z w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«RegChartData».«smoothed_local» := P2M_GroundTheory_Heights__Heights_Regular_RegChartData_smoothed_local_a8630248a862
