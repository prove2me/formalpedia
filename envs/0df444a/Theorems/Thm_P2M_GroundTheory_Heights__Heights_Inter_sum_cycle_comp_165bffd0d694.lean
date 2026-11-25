-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_sum_cycle_comp_165bffd0d694
-- name    : P2M_GroundTheory_Heights__Heights_Inter_sum_cycle_comp_165bffd0d694
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:33.614225+00:00
-- url     : https://prove2.me/theorems/803cf729-d807-49a3-9f58-5d3ce6c3da87
-- title:
--   P2 M Ground Theory Heights  Heights Inter sum cycle comp 165bffd0d694: P2 M Ground Theory Heights  Heights Inter sum cycle comp 165bffd0d694
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter sum cycle comp 165bffd0d694 construction uses the P2 M Ground Theory Heights  Heights Inter sum cycle comp 165bffd0d694 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotLtLtOfMemMinimalPrimes.lean#L157-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotLtLtOfMemMinimalPrimes.lean#L157-L165

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSwap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotLtLtOfMemMinimalPrimes
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
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_sum_cycle_comp_165bffd0d694 {α : Type*} (F : α →₀ ℕ) (G : α → α →₀ ℕ) (c : α → ℝ) :
    (F.sum fun W m => (m : ℝ) * (G W).sum fun U k => (k : ℝ) * c U) =
      (F.sum fun W m => m • G W).sum fun U k => (k : ℝ) * c U := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«sum_cycle_comp» := P2M_GroundTheory_Heights__Heights_Inter_sum_cycle_comp_165bffd0d694
