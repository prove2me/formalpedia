-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_exponentCondition_neg
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.exponentCondition_neg
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:49:43.067915+00:00
-- url     : https://prove2.me/theorems/fca96fa8-2707-4a85-b3f9-098df2081578
-- title:
--   OSAux: exponent Condition neg
-- statement:
--   The OSAux construction uses the exponent Condition neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/ExponentConditionNeg.lean#L42-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/ExponentConditionNeg.lean#L42-L86

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LintegralInsertFiberLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_DeZeroBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ExponentConditionNeg
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
open ReciprocityTheory.ChartRestriction.DS.Xi.OSAux

theorem ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.exponentCondition_neg {p : ℕ} (e : Fin (p + 2) → ℝ) {α : ℝ} (he : ∀ l, 0 < e l)
    (hα : 2 * ∑ i : Fin (p + 1), e i.succ < α) :
    CHCond p (Function.update (fun i : Fin (p + 1) => -e i.succ) 0
        (α + (fun i : Fin (p + 1) => -e i.succ) 0)) ∧
      0 < α + 2 * ∑ i, (fun i : Fin (p + 1) => -e i.succ) i := by sorry
