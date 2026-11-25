-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_subgroupData_sublevel
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.subgroupData.sublevel
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:48:40.849972+00:00
-- url     : https://prove2.me/theorems/54797a7d-f804-4b54-b3c4-c65cf5c6ac7b
-- title:
--   subgroup Data: sublevel
-- statement:
--   The subgroup Data construction uses the sublevel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/PolynomialGrowthIntegrals.lean#L97-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/PolynomialGrowthIntegrals.lean#L97-L138

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_PolynomialGrowthIntegrals
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.subgroupData

theorem ReciprocityTheory.ChartRestriction.DS.Xi.subgroupData.sublevel (c : Fin 3 → ℂ) {la g : ℝ} (hg : 0 < g)
    (hno : ∀ t1 t2 t3 : ℝ, 1 ≤ t1 → t3 ≤ 2 → g ≤ t2 - t1 → g ≤ t3 - t2 → ‖qv c t1‖ ≤ la →
      ‖qv c t2‖ ≤ la → ‖qv c t3‖ ≤ la → False) :
    volume {t | t ∈ Icc (1:ℝ) 2 ∧ ‖qv c t‖ ≤ la} ≤ ENNReal.ofReal (2 * g) := by sorry
