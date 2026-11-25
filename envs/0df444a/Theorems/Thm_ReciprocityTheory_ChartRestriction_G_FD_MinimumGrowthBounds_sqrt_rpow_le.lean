-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MinimumGrowthBounds_sqrt_rpow_le
-- name    : ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds.sqrt_rpow_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:19:16.306594+00:00
-- url     : https://prove2.me/theorems/fa972f35-fe12-5129-bb6d-9fa2fc482c33
-- title:
--   Minimum Growth Bounds: sqrt rpow le
-- statement:
--   The Minimum Growth Bounds construction uses the sqrt rpow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MinimumGrowthBounds.lean#L72-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MinimumGrowthBounds.lean#L72-L103

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TwoSidedBoostBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MinimumGrowthBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex MajorantConjugateTransfer TwoSidedBoostBounds
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds
variable {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds.sqrt_rpow_le (A : ℝ) {k1 k2 L Ly : ℝ} (hk1 : 0 < k1) (hk12 : k1 ≤ k2) (hL : 0 ≤ L)
    (h1 : k1 * L ≤ Ly) (h2 : Ly ≤ k2 * L) :
    Real.sqrt Ly ^ (-A) ≤ max (k1 ^ (-A / 2)) (k2 ^ (-A / 2)) * Real.sqrt L ^ (-A) := by sorry
