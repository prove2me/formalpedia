-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lfa_mul_of_not_disjoint
-- name    : ReciprocityTheory.ChartRestriction.DS.lfa_mul_of_not_disjoint
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:53:32.920709+00:00
-- url     : https://prove2.me/theorems/36f0391c-235d-4925-9f33-17a893501bda
-- title:
--   DS: lfa mul of not disjoint
-- statement:
--   The DS construction uses the lfa mul of not disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockA.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockA.lean#L11-L14

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockA
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

theorem ReciprocityTheory.ChartRestriction.DS.lfa_mul_of_not_disjoint (s t : Finset (Fin (n * n))) (h : ¬ Disjoint s t) :
    fockBasis n s * fockBasis n t = 0 := by sorry
