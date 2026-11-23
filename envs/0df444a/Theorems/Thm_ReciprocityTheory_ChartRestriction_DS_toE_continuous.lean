-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_toE_continuous
-- name    : ReciprocityTheory.ChartRestriction.DS.toE_continuous
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:13:21.467514+00:00
-- url     : https://prove2.me/theorems/5232f378-20bd-4339-a63f-4fb882c898c7
-- title:
--   DS: to E continuous
-- statement:
--   The DS construction uses the to E continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/InhabRep.lean#L146-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/InhabRep.lean#L146-L152

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_InhabRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS

theorem ReciprocityTheory.ChartRestriction.DS.toE_continuous (n : ℕ) : Continuous (toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) := by sorry
