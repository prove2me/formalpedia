-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_summable_prod_mul_pow_div_factorial
-- name    : ReciprocityTheory.ChartRestriction.DS.summable_prod_mul_pow_div_factorial
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:54:19.161194+00:00
-- url     : https://prove2.me/theorems/cfb1c0fa-2f88-5374-be9d-ddf1ddf27a29
-- title:
--   DS: summable prod mul pow div factorial
-- statement:
--   The DS construction uses the summable prod mul pow div factorial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/Series.lean#L11-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/Series.lean#L11-L43

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Series
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Filter
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.summable_prod_mul_pow_div_factorial {A B r : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hr : 0 ≤ r)
    (hrB : r * B < 1) (k : ℕ) :
    Summable fun m : ℕ =>
      (∏ l ∈ range m, (A + B * ((k : ℝ) + l))) * r ^ m / (m.factorial : ℝ) := by sorry
