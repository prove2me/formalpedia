-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_subgroupData_E_closed
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.subgroupData.E_closed
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:09:29.834751+00:00
-- url     : https://prove2.me/theorems/54e4d00b-ff98-46b7-8266-9bdb7803f4a6
-- title:
--   subgroup Data: E closed
-- statement:
--   The subgroup Data construction uses the E closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/PolynomialGrowthIntegrals.lean#L94-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/PolynomialGrowthIntegrals.lean#L94-L95

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.subgroupData.E_closed (c : Fin 3 → ℂ) (la : ℝ) : IsClosed {t | t ∈ Icc (1:ℝ) 2 ∧ ‖qv c t‖ ≤ la} := by sorry
