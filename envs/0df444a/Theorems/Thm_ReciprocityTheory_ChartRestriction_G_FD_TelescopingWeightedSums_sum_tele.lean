-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TelescopingWeightedSums_sum_tele
-- name    : ReciprocityTheory.ChartRestriction.G.FD.TelescopingWeightedSums.sum_tele
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:20:18.454919+00:00
-- url     : https://prove2.me/theorems/a7600a24-c995-5dcf-8175-597af6403c2e
-- title:
--   Telescoping Weighted Sums: sum tele
-- statement:
--   The Telescoping Weighted Sums construction uses the sum tele property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/TelescopingWeightedSums.lean#L6-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/TelescopingWeightedSums.lean#L6-L12

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TelescopingWeightedSums
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.TelescopingWeightedSums
open Finset

theorem ReciprocityTheory.ChartRestriction.G.FD.TelescopingWeightedSums.sum_tele (f : ℕ → ℝ) {p n : ℕ} (hp : p ≤ n) :
    ∑ i ∈ Ico p n, (f (i + 1) - f i) = f n - f p := by sorry
