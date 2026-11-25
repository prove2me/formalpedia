-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lf_mem_phys
-- name    : ReciprocityTheory.ChartRestriction.DS.lf_mem_phys
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:53:15.59125+00:00
-- url     : https://prove2.me/theorems/1c572371-b9e0-431e-9706-b6becf064178
-- title:
--   DS: lf mem phys
-- statement:
--   The DS construction uses the lf mem phys property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockB.lean#L63-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockB.lean#L63-L65

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

theorem ReciprocityTheory.ChartRestriction.DS.lf_mem_phys (ε : Fin n → Bool) (i a : Fin n) :
    finProdFinEquiv (i, a) ∈ lfPhysModes ε ↔ ε i = true ∧ ε a = false := by sorry
