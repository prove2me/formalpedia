-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_logSumExp_lower
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.logSumExp_lower
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:45:44.683799+00:00
-- url     : https://prove2.me/theorems/fd3a2bd9-fe32-4573-85f6-be8fc86b4b7f
-- title:
--   S7: log Sum Exp lower
-- statement:
--   The S7 construction uses the log Sum Exp lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/DecLog.lean#L32-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/DecLog.lean#L32-L97

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecLog
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.S7.logSumExp_lower {ι : Type*} [Fintype ι] (w y : ι → ℝ) (hw : ∀ j, 0 ≤ w j)
    (h1 : ∑ j, w j = 1) (h0 : ∑ j, w j * y j = 0) {R : ℝ} (hR : 0 < R) (hy : ∀ j, |y j| ≤ R) :
    min 1 (1 / R) * (∑ j, w j * y j ^ 2) / 4 ≤ Real.log (∑ j, w j * Real.exp (y j)) := by sorry
