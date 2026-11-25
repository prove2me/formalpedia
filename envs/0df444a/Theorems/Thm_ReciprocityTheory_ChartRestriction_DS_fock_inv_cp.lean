-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_fock_inv_cp
-- name    : ReciprocityTheory.ChartRestriction.DS.fock_inv_cp
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:52:07.159738+00:00
-- url     : https://prove2.me/theorems/a1e92f6c-bb77-548f-ac89-c755e23daf98
-- title:
--   DS: fock inv cp
-- statement:
--   The DS construction uses the fock inv cp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/FockTA.lean#L95-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/FockTA.lean#L95-L99

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

theorem ReciprocityTheory.ChartRestriction.DS.fock_inv_cp (i a : Fin n) :
    (CliffordAlgebra.involute : Fock n →ₐ[ℂ] Fock n).toLinearMap * cpFock i a =
      -(cpFock i a * (CliffordAlgebra.involute : Fock n →ₐ[ℂ] Fock n).toLinearMap) := by sorry
