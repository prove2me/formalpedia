-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_FrequencyIndexing_eq__k_307b28da5f4e
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_FD_FrequencyIndexing_eq__k_307b28da5f4e
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:18:36.393789+00:00
-- url     : https://prove2.me/theorems/b0084931-de32-4f4e-b6df-b2801bb37e8b
-- title:
--   P2 M Reciprocity Theory Chart Restriction G FD Frequency Indexing eq  k 307b28da5f4e: P2 M Reciprocity Theory Chart Restriction G FD Frequency Indexing eq  k 307b28da5f4e
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G FD Frequency Indexing eq  k 307b28da5f4e construction uses the P2 M Reciprocity Theory Chart Restriction G FD Frequency Indexing eq  k 307b28da5f4e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FrequencyIndexing.lean#L55-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FrequencyIndexing.lean#L55-L63

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_FD_FrequencyIndexing_eq__k_307b28da5f4e (ν : ι → ℝ) (k : Fin n → ℤ) (hk : ∀ j, 2 * ∑ τ, ν τ * ω j τ = k j) : ν = νk ω k := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«FD».«FrequencyIndexing».«eq_νk» := P2M_ReciprocityTheory_ChartRestriction_G_FD_FrequencyIndexing_eq__k_307b28da5f4e
