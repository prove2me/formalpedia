-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_FrequencyIndexing__k_injective_ab739a144fb6
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_FD_FrequencyIndexing__k_injective_ab739a144fb6
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:18:07.250088+00:00
-- url     : https://prove2.me/theorems/49c5b70c-2e08-456a-be91-98f3c95716f3
-- title:
--   P2 M Reciprocity Theory Chart Restriction G FD Frequency Indexing  k injective ab739a144fb6: P2 M Reciprocity Theory Chart Restriction G FD Frequency Indexing  k injective ab739a144fb6
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G FD Frequency Indexing  k injective ab739a144fb6 construction uses the P2 M Reciprocity Theory Chart Restriction G FD Frequency Indexing  k injective ab739a144fb6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FrequencyIndexing.lean#L47-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FrequencyIndexing.lean#L47-L53

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_FD_FrequencyIndexing__k_injective_ab739a144fb6 : Function.Injective (νk ω) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«FD».«FrequencyIndexing».«νk_injective» := P2M_ReciprocityTheory_ChartRestriction_G_FD_FrequencyIndexing__k_injective_ab739a144fb6
