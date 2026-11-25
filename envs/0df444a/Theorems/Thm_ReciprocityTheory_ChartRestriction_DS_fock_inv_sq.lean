-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_fock_inv_sq
-- name    : ReciprocityTheory.ChartRestriction.DS.fock_inv_sq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:53:37.332191+00:00
-- url     : https://prove2.me/theorems/1278faf6-1d6b-5021-9fce-d85897a75af6
-- title:
--   DS: fock inv sq
-- statement:
--   The DS construction uses the fock inv sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/FockTA.lean#L90-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/FockTA.lean#L90-L93

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_InhabCAR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARUnit
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_FockTA
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

theorem ReciprocityTheory.ChartRestriction.DS.fock_inv_sq :
    (CliffordAlgebra.involute : Fock n →ₐ[ℂ] Fock n).toLinearMap *
      (CliffordAlgebra.involute : Fock n →ₐ[ℂ] Fock n).toLinearMap = 1 := by sorry
