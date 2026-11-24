-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MinimumGrowthBounds_nfac_pos
-- name    : ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds.nfac_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:54.333949+00:00
-- url     : https://prove2.me/theorems/eddaa3ce-cd7b-4257-9fa0-d00ef32fe209
-- title:
--   Minimum Growth Bounds: nfac pos
-- statement:
--   The Minimum Growth Bounds construction uses the nfac pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MinimumGrowthBounds.lean#L105-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MinimumGrowthBounds.lean#L105-L113

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

theorem ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds.nfac_pos (la : Wt X.Ψ r) {y : Frame X.Ψ r} (hy : y ∈ X.dom) : 0 < X.nfac la y := by sorry
