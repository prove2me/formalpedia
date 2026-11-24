-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_eeV_comm
-- name    : ReciprocityTheory.ChartRestriction.DS.eeV_comm
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:29:13.125096+00:00
-- url     : https://prove2.me/theorems/f1535da0-7d6e-4a02-a18a-591831fc670c
-- title:
--   DS: ee V comm
-- statement:
--   The DS construction uses the ee V comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/TensorV.lean#L112-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/TensorV.lean#L112-L120

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_TensorV
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

theorem ReciprocityTheory.ChartRestriction.DS.eeV_comm {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) (a b : Fin n) :
    tensV E a b * eeV E = eeV E * tensV E a b := by sorry
