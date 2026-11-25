-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_antiE_hw
-- name    : ReciprocityTheory.ChartRestriction.DS.antiE_hw
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:51:14.899532+00:00
-- url     : https://prove2.me/theorems/f5771644-0cf9-533c-b2f6-5ed75bd0a86f
-- title:
--   DS: anti E hw
-- statement:
--   The DS construction uses the anti E hw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/AntiEIsGlRep.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/AntiEIsGlRep.lean#L23-L27

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_AntiEIsGlRep
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
variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem ReciprocityTheory.ChartRestriction.DS.antiE_hw {E : Fin n → Fin n → Module.End ℂ M} {ν : Fin n → ℝ} {v : M} (hv : IsHWVec E ν v) :
    IsHWVec (antiE E) (fun r => -ν (Fin.rev r)) v := by sorry
