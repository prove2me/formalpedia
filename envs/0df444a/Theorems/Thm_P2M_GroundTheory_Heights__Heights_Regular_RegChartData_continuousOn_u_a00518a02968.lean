-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RegChartData_continuousOn_u_a00518a02968
-- name    : P2M_GroundTheory_Heights__Heights_Regular_RegChartData_continuousOn_u_a00518a02968
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:50.449423+00:00
-- url     : https://prove2.me/theorems/9bf0deca-9455-4e31-9fa9-5f737f0b1c69
-- title:
--   P2 M Ground Theory Heights  Heights Regular Reg Chart Data continuous On u a00518a02968: P2 M Ground Theory Heights  Heights Regular Reg Chart Data continuous On u a00518a02968
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Reg Chart Data continuous On u a00518a02968 construction uses the P2 M Ground Theory Heights  Heights Regular Reg Chart Data continuous On u a00518a02968 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/GlueCharts.lean#L117-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/GlueCharts.lean#L117-L126

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

theorem P2M_GroundTheory_Heights__Heights_Regular_RegChartData_continuousOn_u_a00518a02968 (j : Fin R.N) :
    ContinuousOn (R.u j) ((R.chart j).target \ coordDiv (R.S j)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«RegChartData».«continuousOn_u» := P2M_GroundTheory_Heights__Heights_Regular_RegChartData_continuousOn_u_a00518a02968
