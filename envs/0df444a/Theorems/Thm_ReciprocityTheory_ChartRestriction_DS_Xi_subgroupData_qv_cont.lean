-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_subgroupData_qv_cont
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.subgroupData.qv_cont
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:48:41.416879+00:00
-- url     : https://prove2.me/theorems/7ec30e54-e7ff-4ebb-b3df-d6e883102b82
-- title:
--   subgroup Data: qv cont
-- statement:
--   The subgroup Data construction uses the qv cont property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/PolynomialGrowthIntegrals.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/PolynomialGrowthIntegrals.lean#L13-L14

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.subgroupData.qv_cont (c : Fin 3 → ℂ) : Continuous (qv c) := by sorry
