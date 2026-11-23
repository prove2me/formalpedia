-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lfMatFull_eq_zero
-- name    : ReciprocityTheory.ChartRestriction.DS.lfMatFull_eq_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:11:44.960653+00:00
-- url     : https://prove2.me/theorems/6842d84b-eee8-4e3a-bea3-33d37d05bc5a
-- title:
--   DS: lf Mat Full eq zero
-- statement:
--   The DS construction uses the lf Mat Full eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockB.lean#L94-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockB.lean#L94-L106

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockA
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockB
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
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.lfMatFull_eq_zero (ε : Fin n → Bool) (a b : Fin n) {S T : Finset (Fin (n * n))}
    (hS : S ⊆ lfPhysModes ε) (hT : ¬ T ⊆ lfPhysModes ε) : lfMatFull ε a b T S = 0 := by sorry
