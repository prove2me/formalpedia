-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_mIntCongrNull
-- name    : ReciprocityTheory.AnForm.M.mIntCongrNull
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:31:43.889802+00:00
-- url     : https://prove2.me/theorems/d77b41bd-57f7-47a1-b247-2b046358eaae
-- title:
--   M: m Int Congr Null
-- statement:
--   The M construction uses the m Int Congr Null property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/AnalyticSubsetChartLocal.lean#L89-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/AnalyticSubsetChartLocal.lean#L89-L95

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

theorem ReciprocityTheory.AnForm.M.mIntCongrNull : MIntCongrNullStatement := by sorry
