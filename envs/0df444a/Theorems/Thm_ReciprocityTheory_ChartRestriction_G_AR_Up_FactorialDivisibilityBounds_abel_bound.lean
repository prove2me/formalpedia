-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_FactorialDivisibilityBounds_abel_bound
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.FactorialDivisibilityBounds.abel_bound
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:05:51.986056+00:00
-- url     : https://prove2.me/theorems/532f28bf-a91c-5861-9b2b-9e58cd1703e8
-- title:
--   Factorial Divisibility Bounds: abel bound
-- statement:
--   The Factorial Divisibility Bounds construction uses the abel bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/CuspStatementPf.lean#L16-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/CuspStatementPf.lean#L16-L37

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowCoefficientBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspCoefficientFlow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HolomorphicPeriodicityExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FjFlow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_CuspStatementPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits
  ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms
noncomputable section
open ReciprocityTheory.ChartRestriction.G.AR.Up.FactorialDivisibilityBounds

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.FactorialDivisibilityBounds.abel_bound (a L : ℕ → ℝ) (p r : ℕ) (hL : ∀ k ≤ r, L k ≤ L p)
    (hgap : ∀ k, 1 ≤ k → k < r → k ≠ p → a k ≤ a (k - 1)) :
    ∀ n, 1 ≤ n → n ≤ r → ∑ k ∈ Finset.range n, a k * (L (k + 1) - L k) ≤
      a (n - 1) * L n - a 0 * L 0 + (a 0 - a (n - 1)) * L p := by sorry
