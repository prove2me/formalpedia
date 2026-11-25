-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_ExponentialGrowthExclusion_exists_fd
-- name    : ReciprocityTheory.ChartRestriction.G.FD.ExponentialGrowthExclusion.exists_fd
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:13:31.226435+00:00
-- url     : https://prove2.me/theorems/655d2f6d-ec53-40e9-8eff-4c26a1fd3681
-- title:
--   Exponential Growth Exclusion: exists fd
-- statement:
--   The Exponential Growth Exclusion construction uses the exists fd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/ExponentialGrowthExclusion.lean#L12-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/ExponentialGrowthExclusion.lean#L12-L29

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealEmbeddingCharacters
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExponentialGrowthExclusion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.ExponentialGrowthExclusion
open NumberField Complex MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.FD
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.FD.ExponentialGrowthExclusion.exists_fd (X : Data E r) (la : Wt X.Ψ r) :
    ∃ D : Set (X.Ψ → ℝ), MeasurableSet D ∧ IsAddFundamentalDomain (X.periods la) D volume ∧
      0 < volume D ∧ volume D < ⊤ := by sorry
