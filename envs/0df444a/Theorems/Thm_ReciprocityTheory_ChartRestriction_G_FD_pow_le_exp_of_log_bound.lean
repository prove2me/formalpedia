-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_pow_le_exp_of_log_bound
-- name    : ReciprocityTheory.ChartRestriction.G.FD.pow_le_exp_of_log_bound
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:21:41.726365+00:00
-- url     : https://prove2.me/theorems/e1930d22-920b-4e8c-949a-07ccc04e4c96
-- title:
--   FD: pow le exp of log bound
-- statement:
--   The FD construction uses the pow le exp of log bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/CountingExponentialSumHolds.lean#L7-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/CountingExponentialSumHolds.lean#L7-L27

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CountingExponentialSumHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open Finset

theorem ReciprocityTheory.ChartRestriction.G.FD.pow_le_exp_of_log_bound {K N w m : ℝ} (hK : 1 ≤ K) (hN : 1 ≤ N) (hw : 0 ≤ w)
    (hm : w + N * Real.log (2 * K * N) + N + 2 ≤ m) :
    (K * m) ^ N ≤ Real.exp (2 * m - w - 2) := by sorry
