-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_nsq_root
-- name    : ReciprocityTheory.ChartRestriction.DS.nsq_root
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:38:31.362855+00:00
-- url     : https://prove2.me/theorems/6f1ae1e8-5753-4fbc-8c86-d57b47daee05
-- title:
--   DS: nsq root
-- statement:
--   The DS construction uses the nsq root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/NumRho.lean#L175-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/NumRho.lean#L175-L177

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NumRho
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

theorem ReciprocityTheory.ChartRestriction.DS.nsq_root {a b : Fin n} (hab : a ≠ b) : nsq (root a b) = 2 := by sorry
