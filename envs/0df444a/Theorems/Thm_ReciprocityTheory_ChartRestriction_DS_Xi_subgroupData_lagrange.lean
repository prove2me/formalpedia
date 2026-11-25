-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_subgroupData_lagrange
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.subgroupData.lagrange
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:48:51.371831+00:00
-- url     : https://prove2.me/theorems/43d518be-3bac-4ee8-b844-5ef7b7ef0830
-- title:
--   subgroup Data: lagrange
-- statement:
--   The subgroup Data construction uses the lagrange property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/PolynomialGrowthIntegrals.lean#L24-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/PolynomialGrowthIntegrals.lean#L24-L92

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.subgroupData.lagrange (c : Fin 3 → ℂ) {t1 t2 t3 g la : ℝ} (hg : 0 < g) (h1 : 1 ≤ t1) (h3 : t3 ≤ 2)
    (h12 : g ≤ t2 - t1) (h23 : g ≤ t3 - t2)
    (p1 : ‖qv c t1‖ ≤ la) (p2 : ‖qv c t2‖ ≤ la) (p3 : ‖qv c t3‖ ≤ la) :
    ‖c‖ ≤ 12 * la / g ^ 2 := by sorry
