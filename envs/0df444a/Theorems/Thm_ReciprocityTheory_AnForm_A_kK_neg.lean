-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_kK_neg
-- name    : ReciprocityTheory.AnForm.A.kK_neg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:01:07.049803+00:00
-- url     : https://prove2.me/theorems/32bfac4a-ad03-4b44-aeea-69e8ebbba67e
-- title:
--   A: k K neg
-- statement:
--   The A construction uses the k K neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L110-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L110-L111

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

theorem ReciprocityTheory.AnForm.A.kK_neg (h : ι → ℝ) : kK (-h) = kK h := by sorry
