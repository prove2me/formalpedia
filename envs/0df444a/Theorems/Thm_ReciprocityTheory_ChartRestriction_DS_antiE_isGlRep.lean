-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_antiE_isGlRep
-- name    : ReciprocityTheory.ChartRestriction.DS.antiE_isGlRep
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:50:59.789804+00:00
-- url     : https://prove2.me/theorems/aebf173b-4390-5b2d-97aa-c0fdf715e7b0
-- title:
--   DS: anti E is Gl Rep
-- statement:
--   The DS construction uses the anti E is Gl Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/AntiEIsGlRep.lean#L14-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/AntiEIsGlRep.lean#L14-L21

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

theorem ReciprocityTheory.ChartRestriction.DS.antiE_isGlRep {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) : IsGlRep (antiE E) := by sorry
