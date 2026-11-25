-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_FrequencyIndexing__k_spec_f7cb7fb69995
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_FD_FrequencyIndexing__k_spec_f7cb7fb69995
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:41:41.342663+00:00
-- url     : https://prove2.me/theorems/b6f29ca5-0990-4060-9390-7e2e3b9c14da
-- title:
--   P2 M Reciprocity Theory Chart Restriction G FD Frequency Indexing  k spec f7cb7fb69995: P2 M Reciprocity Theory Chart Restriction G FD Frequency Indexing  k spec f7cb7fb69995
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G FD Frequency Indexing  k spec f7cb7fb69995 construction uses the P2 M Reciprocity Theory Chart Restriction G FD Frequency Indexing  k spec f7cb7fb69995 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FrequencyIndexing.lean#L33-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FrequencyIndexing.lean#L33-L45

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_FD_FrequencyIndexing__k_spec_f7cb7fb69995 (k : Fin n → ℤ) (i : Fin n) : 2 * ∑ τ, νk ω k τ * ω i τ = k i := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«FD».«FrequencyIndexing».«νk_spec» := P2M_ReciprocityTheory_ChartRestriction_G_FD_FrequencyIndexing__k_spec_f7cb7fb69995
