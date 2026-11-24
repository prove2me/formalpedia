-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_kK_hasCompactSupport
-- name    : ReciprocityTheory.AnForm.A.kK_hasCompactSupport
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:21.570942+00:00
-- url     : https://prove2.me/theorems/653c1a02-16d4-4f5f-940e-2f400f26b2fe
-- title:
--   A: k K has Compact Support
-- statement:
--   The A construction uses the k K has Compact Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L121-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L121-L124

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology
open scoped ContDiff Interval
noncomputable section
variable {ι : Type*} [Fintype ι]

theorem ReciprocityTheory.AnForm.A.kK_hasCompactSupport : HasCompactSupport (kK : (ι → ℝ) → ℝ) := by sorry
