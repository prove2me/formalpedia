-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_isNCSum_zero
-- name    : ReciprocityTheory.ChartRestriction.DS.isNCSum_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:50:53.631697+00:00
-- url     : https://prove2.me/theorems/083376a1-e50a-47cf-b550-89404c949995
-- title:
--   DS: is NCSum zero
-- statement:
--   The DS construction uses the is NCSum zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/Numerics.lean#L130-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/Numerics.lean#L130-L135

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NumRho
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Numerics
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {ε : Fin n → Bool}

theorem ReciprocityTheory.ChartRestriction.DS.isNCSum_zero {ν : Fin n → ℝ} : IsNCSum ε 0 ν ↔ ν = 0 := by sorry
