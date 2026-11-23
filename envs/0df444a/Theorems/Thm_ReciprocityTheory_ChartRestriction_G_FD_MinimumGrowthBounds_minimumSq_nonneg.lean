-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MinimumGrowthBounds_minimumSq_nonneg
-- name    : ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds.minimumSq_nonneg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:23:27.636377+00:00
-- url     : https://prove2.me/theorems/9befdd6f-6f49-467c-8fb9-d960d7723ee9
-- title:
--   Minimum Growth Bounds: minimum Sq nonneg
-- statement:
--   The Minimum Growth Bounds construction uses the minimum Sq nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MinimumGrowthBounds.lean#L14-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MinimumGrowthBounds.lean#L14-L18

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

theorem ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds.minimumSq_nonneg {x : Frame X.Ψ r} (hx : x ∈ X.dom) : 0 ≤ X.firstMinimumSq x := by sorry
