-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_isNCSum_succ_exists
-- name    : ReciprocityTheory.ChartRestriction.DS.isNCSum_succ_exists
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:13:54.100679+00:00
-- url     : https://prove2.me/theorems/a6d4e778-7023-4ac6-9da7-5fba0a7086cb
-- title:
--   DS: is NCSum succ exists
-- statement:
--   The DS construction uses the is NCSum succ exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/Numerics.lean#L137-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/Numerics.lean#L137-L140

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

theorem ReciprocityTheory.ChartRestriction.DS.isNCSum_succ_exists {k : ℕ} {ν : Fin n → ℝ} (hν : IsNCSum ε (k + 1) ν) :
    ∃ a b : Fin n, ε a ≠ ε b := by sorry
