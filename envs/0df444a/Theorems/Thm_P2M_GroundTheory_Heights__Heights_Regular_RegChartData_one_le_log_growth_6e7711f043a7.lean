-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RegChartData_one_le_log_growth_6e7711f043a7
-- name    : P2M_GroundTheory_Heights__Heights_Regular_RegChartData_one_le_log_growth_6e7711f043a7
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:17:38.969794+00:00
-- url     : https://prove2.me/theorems/8afc2427-bdba-4748-bb10-fca34e44fc46
-- title:
--   P2 M Ground Theory Heights  Heights Regular Reg Chart Data one le log growth 6e7711f043a7: P2 M Ground Theory Heights  Heights Regular Reg Chart Data one le log growth 6e7711f043a7
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Reg Chart Data one le log growth 6e7711f043a7 construction uses the P2 M Ground Theory Heights  Heights Regular Reg Chart Data one le log growth 6e7711f043a7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PTruncPsh.lean#L18-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PTruncPsh.lean#L18-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StatementsTruncPsh
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_GlueCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PTruncPsh
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
open ReciprocityTheory.AnForm.A (IsPsh coordDiv limsupExt)
open ReciprocityTheory.AnForm.M (FinHolAtlas)
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.RegChartData
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X} (R : RegChartData A)

theorem P2M_GroundTheory_Heights__Heights_Regular_RegChartData_one_le_log_growth_6e7711f043a7 (j : Fin R.N) {y : Fin D → ℂ} (hyt : y ∈ (R.chart j).target) :
    1 ≤ Real.log (Real.exp 1 + ∑ i ∈ R.S j, Real.log ‖y i‖⁻¹) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«RegChartData».«one_le_log_growth» := P2M_GroundTheory_Heights__Heights_Regular_RegChartData_one_le_log_growth_6e7711f043a7
