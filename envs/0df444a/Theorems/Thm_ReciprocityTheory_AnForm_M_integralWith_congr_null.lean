-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_integralWith_congr_null
-- name    : ReciprocityTheory.AnForm.M.integralWith_congr_null
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:19:22.28706+00:00
-- url     : https://prove2.me/theorems/7fedd4a9-8409-535e-b0c8-8478679f8375
-- title:
--   M: integral With congr null
-- statement:
--   The M construction uses the integral With congr null property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/AnalyticSubsetChartLocal.lean#L60-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/AnalyticSubsetChartLocal.lean#L60-L87

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_NullZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_AnalyticSubsetChartLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
noncomputable section

theorem ReciprocityTheory.AnForm.M.integralWith_congr_null {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (P : ChartPartition A) (Φ : Fin e → LocPot X) {S : Set X} (hS : A.IsAnalyticSubset S)
    (hint : interior S = ∅) {g g' : X → ℝ} (hg : ∀ x ∉ S, g x = g' x) :
    integralWith A P Φ g = integralWith A P Φ g' := by sorry
