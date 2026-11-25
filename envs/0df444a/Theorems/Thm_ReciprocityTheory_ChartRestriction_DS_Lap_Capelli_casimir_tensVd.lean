-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_casimir_tensVd
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.casimir_tensVd
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:42:35.245231+00:00
-- url     : https://prove2.me/theorems/0e259402-f9ee-430e-a946-f3459d12e8b2
-- title:
--   Capelli: casimir tens Vd
-- statement:
--   The Capelli construction uses the casimir tens Vd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/Tensor.lean#L70-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/Tensor.lean#L70-L85

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_Expand
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_Tensor
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
open ReciprocityTheory.ChartRestriction.DS
variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.casimir_tensVd {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) :
    casimir (tensVd E) f = (fun d => casimir E (f d)) + ((n : ℂ) • f + (2 : ℂ) • eeVd E f) := by sorry
