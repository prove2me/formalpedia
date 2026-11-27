-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TelescopingWeightedSums_wsum_bound
-- name    : ReciprocityTheory.ChartRestriction.G.FD.TelescopingWeightedSums.wsum_bound
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:13:05.537055+00:00
-- url     : https://prove2.me/theorems/f40427d1-1f58-5f02-8104-6d084db2ae8f
-- title:
--   Telescoping Weighted Sums: wsum bound
-- statement:
--   The Telescoping Weighted Sums construction uses the wsum bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/TelescopingWeightedSums.lean#L33-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/TelescopingWeightedSums.lean#L33-L90

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

theorem ReciprocityTheory.ChartRestriction.G.FD.TelescopingWeightedSums.wsum_bound {n p : ℕ} (hp : p ≤ n) (ρ : ℕ → ℝ) (hρ : ∀ i ≤ n, 0 < ρ i) (h0 : ρ 0 = 1)
    (hn : ρ n = 1)
    (hmono : ((∀ i, i < p → ρ i ≤ ρ (i + 1)) ∧ ∀ i, p ≤ i → i < n → ρ (i + 1) ≤ ρ i) ∨
      ((∀ i, i < p → ρ (i + 1) ≤ ρ i) ∧ ∀ i, p ≤ i → i < n → ρ i ≤ ρ (i + 1)))
    (a : ℕ → ℝ) (lo hi : ℝ) (ha : ∀ i < n, lo ≤ a i ∧ a i ≤ hi) :
    |∑ i ∈ range n, a i * (Real.log (ρ (i + 1)) - Real.log (ρ i))| ≤
      (hi - lo) * |Real.log (ρ p)| := by sorry
