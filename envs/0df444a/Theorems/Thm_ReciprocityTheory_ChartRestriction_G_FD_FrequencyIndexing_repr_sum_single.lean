-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrequencyIndexing_repr_sum_single
-- name    : ReciprocityTheory.ChartRestriction.G.FD.FrequencyIndexing.repr_sum_single
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:18:20.998257+00:00
-- url     : https://prove2.me/theorems/ad26f7a3-7304-5ab9-9821-341e719b6998
-- title:
--   Frequency Indexing: repr sum single
-- statement:
--   The Frequency Indexing construction uses the repr sum single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FrequencyIndexing.lean#L23-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FrequencyIndexing.lean#L23-L31

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TubeFourierExpansion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FrequencyIndexing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrequencyIndexing
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (ω : Module.Basis (Fin n) ℝ (ι → ℝ))

theorem ReciprocityTheory.ChartRestriction.G.FD.FrequencyIndexing.repr_sum_single (v : ι → ℝ) (j : Fin n) :
    ∑ τ, v τ * ω.repr (Pi.single τ 1) j = ω.repr v j := by sorry
