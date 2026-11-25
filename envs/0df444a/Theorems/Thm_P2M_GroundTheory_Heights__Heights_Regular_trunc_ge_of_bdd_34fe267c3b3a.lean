-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_trunc_ge_of_bdd_34fe267c3b3a
-- name    : P2M_GroundTheory_Heights__Heights_Regular_trunc_ge_of_bdd_34fe267c3b3a
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:18:48.933291+00:00
-- url     : https://prove2.me/theorems/6d9d108b-6266-4305-9d78-a07033ab4c1c
-- title:
--   P2 M Ground Theory Heights  Heights Regular trunc ge of bdd 34fe267c3b3a: P2 M Ground Theory Heights  Heights Regular trunc ge of bdd 34fe267c3b3a
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular trunc ge of bdd 34fe267c3b3a construction uses the P2 M Ground Theory Heights  Heights Regular trunc ge of bdd 34fe267c3b3a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PChartMollifiedBounds.lean#L16-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PChartMollifiedBounds.lean#L16-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StatementsChartBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StatementsTruncPsh
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PChartMollifiedBounds
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
open Metric Filter Topology MeasureTheory Set
open ReciprocityTheory.AnForm.A (IsPsh Mollifier molli coordDiv limsupExt polyMax shrink)
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Regular_trunc_ge_of_bdd_34fe267c3b3a {D : ℕ} {X : Type*} [TopologicalSpace X] {A : ReciprocityTheory.AnForm.M.FinHolAtlas D X}
    (R : RegChartData A) (K B : ℝ) (j : Fin R.N) {V : Set (Fin D → ℂ)} (hVo : IsOpen V)
    (hVt : V ⊆ (R.chart j).target) (hb : ∀ y ∈ V, R.trunc K j y ≤ B) {y : Fin D → ℂ} (hy : y ∈ V) :
    -K ≤ R.trunc K j y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«trunc_ge_of_bdd» := P2M_GroundTheory_Heights__Heights_Regular_trunc_ge_of_bdd_34fe267c3b3a
