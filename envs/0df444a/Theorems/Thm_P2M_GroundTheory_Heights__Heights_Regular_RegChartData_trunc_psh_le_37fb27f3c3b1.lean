-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RegChartData_trunc_psh_le_37fb27f3c3b1
-- name    : P2M_GroundTheory_Heights__Heights_Regular_RegChartData_trunc_psh_le_37fb27f3c3b1
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:18:08.693216+00:00
-- url     : https://prove2.me/theorems/2620e947-c777-4c37-9ff9-c76a90fca7f9
-- title:
--   P2 M Ground Theory Heights  Heights Regular Reg Chart Data trunc psh le 37fb27f3c3b1: P2 M Ground Theory Heights  Heights Regular Reg Chart Data trunc psh le 37fb27f3c3b1
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Reg Chart Data trunc psh le 37fb27f3c3b1 construction uses the P2 M Ground Theory Heights  Heights Regular Reg Chart Data trunc psh le 37fb27f3c3b1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PTruncPsh.lean#L27-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PTruncPsh.lean#L27-L63

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

theorem P2M_GroundTheory_Heights__Heights_Regular_RegChartData_trunc_psh_le_37fb27f3c3b1 (j : Fin R.N) {V : Set (Fin D → ℂ)} (hV : IsOpen V)
    (hVt : V ⊆ (R.chart j).target) {B : ℝ} (hB : ∀ y ∈ V \ coordDiv (R.S j), R.u j y ≤ B)
    (K : ℝ) : IsPsh V (R.trunc K j) ∧ ∀ y ∈ V, R.trunc K j y ≤ max B (-K) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«RegChartData».«trunc_psh_le» := P2M_GroundTheory_Heights__Heights_Regular_RegChartData_trunc_psh_le_37fb27f3c3b1
