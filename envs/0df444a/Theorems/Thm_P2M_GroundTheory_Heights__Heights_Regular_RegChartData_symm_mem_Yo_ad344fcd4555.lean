-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RegChartData_symm_mem_Yo_ad344fcd4555
-- name    : P2M_GroundTheory_Heights__Heights_Regular_RegChartData_symm_mem_Yo_ad344fcd4555
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:36:29.126401+00:00
-- url     : https://prove2.me/theorems/c618db81-1a73-45fc-8b48-f773b17cee45
-- title:
--   P2 M Ground Theory Heights  Heights Regular Reg Chart Data symm mem Yo ad344fcd4555: P2 M Ground Theory Heights  Heights Regular Reg Chart Data symm mem Yo ad344fcd4555
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Reg Chart Data symm mem Yo ad344fcd4555 construction uses the P2 M Ground Theory Heights  Heights Regular Reg Chart Data symm mem Yo ad344fcd4555 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/GlueCharts.lean#L113-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/GlueCharts.lean#L113-L115

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

theorem P2M_GroundTheory_Heights__Heights_Regular_RegChartData_symm_mem_Yo_ad344fcd4555 (j : Fin R.N) {y : Fin D → ℂ} (hy : y ∈ (R.chart j).target)
    (hyA : y ∉ coordDiv (R.S j)) : (R.chart j).symm y ∈ R.Yo := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«RegChartData».«symm_mem_Yo» := P2M_GroundTheory_Heights__Heights_Regular_RegChartData_symm_mem_Yo_ad344fcd4555
