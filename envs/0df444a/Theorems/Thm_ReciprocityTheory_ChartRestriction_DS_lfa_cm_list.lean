-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lfa_cm_list
-- name    : ReciprocityTheory.ChartRestriction.DS.lfa_cm_list
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:53:13.919964+00:00
-- url     : https://prove2.me/theorems/9a80463d-d0f4-4259-b9a7-d53f579252d5
-- title:
--   DS: lfa cm list
-- statement:
--   The DS construction uses the lfa cm list property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockA.lean#L50-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockA.lean#L50-L59

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

theorem ReciprocityTheory.ChartRestriction.DS.lfa_cm_list (x : Fin n × Fin n) (l : List (Fin n × Fin n)) (hx : x ∉ l) :
    cmFock x.1 x.2 (l.map fun y => ExteriorAlgebra.ι ℂ (Pi.single y (1 : ℂ))).prod = 0 := by sorry
