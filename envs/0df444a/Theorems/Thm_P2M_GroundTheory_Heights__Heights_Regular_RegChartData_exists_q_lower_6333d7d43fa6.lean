-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RegChartData_exists_q_lower_6333d7d43fa6
-- name    : P2M_GroundTheory_Heights__Heights_Regular_RegChartData_exists_q_lower_6333d7d43fa6
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:30:29.648294+00:00
-- url     : https://prove2.me/theorems/077df9d7-78d5-5d45-8f92-765b6a116bd0
-- title:
--   P2 M Ground Theory Heights  Heights Regular Reg Chart Data exists q lower 6333d7d43fa6: P2 M Ground Theory Heights  Heights Regular Reg Chart Data exists q lower 6333d7d43fa6
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Reg Chart Data exists q lower 6333d7d43fa6 construction uses the P2 M Ground Theory Heights  Heights Regular Reg Chart Data exists q lower 6333d7d43fa6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PMollifiedNearSmooth.lean#L21-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PMollifiedNearSmooth.lean#L21-L38

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

theorem P2M_GroundTheory_Heights__Heights_Regular_RegChartData_exists_q_lower_6333d7d43fa6 [CompactSpace X] :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ j, ∀ x ∈ R.mid j, -Q ≤ R.q j (R.chart j x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«RegChartData».«exists_q_lower» := P2M_GroundTheory_Heights__Heights_Regular_RegChartData_exists_q_lower_6333d7d43fa6
