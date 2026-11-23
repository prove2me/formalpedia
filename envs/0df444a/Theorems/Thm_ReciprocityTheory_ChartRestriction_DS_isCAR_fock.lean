-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_isCAR_fock
-- name    : ReciprocityTheory.ChartRestriction.DS.isCAR_fock
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:52:09.236283+00:00
-- url     : https://prove2.me/theorems/3b570a5d-8770-43cc-8dc4-17b6e7406ac9
-- title:
--   DS: is CAR fock
-- statement:
--   The DS construction uses the is CAR fock property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/InhabCAR.lean#L19-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/InhabCAR.lean#L19-L37

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CarSumSqZeroOfAnti
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_InhabCAR
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

theorem ReciprocityTheory.ChartRestriction.DS.isCAR_fock : IsCAR (cpFock (n := n)) cmFock := by sorry
