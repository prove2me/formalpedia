-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrequencyIndexing_pairing
-- name    : ReciprocityTheory.ChartRestriction.G.FD.FrequencyIndexing.pairing
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:18:28.221392+00:00
-- url     : https://prove2.me/theorems/89664dfe-f314-591e-9af0-cd13329590fd
-- title:
--   Frequency Indexing: pairing
-- statement:
--   The Frequency Indexing construction uses the pairing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FrequencyIndexing.lean#L10-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FrequencyIndexing.lean#L10-L21

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

theorem ReciprocityTheory.ChartRestriction.G.FD.FrequencyIndexing.pairing (ν : ι → ℝ) (k : Fin n → ℤ) (hk : ∀ j, 2 * ∑ τ, ν τ * ω j τ = k j) (v : ι → ℝ) :
    ∑ τ, ν τ * v τ = (∑ j, (k j : ℝ) * ω.repr v j) / 2 := by sorry
