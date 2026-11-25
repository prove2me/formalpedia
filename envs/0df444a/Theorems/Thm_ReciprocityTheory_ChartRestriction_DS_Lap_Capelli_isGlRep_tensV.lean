-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_isGlRep_tensV
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.isGlRep_tensV
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:43:04.737808+00:00
-- url     : https://prove2.me/theorems/0efc81da-94eb-49ee-8175-dd9efebf6ee3
-- title:
--   Capelli: is Gl Rep tens V
-- statement:
--   The Capelli construction uses the is Gl Rep tens V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/Tensor.lean#L31-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/Tensor.lean#L31-L40

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

theorem ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.isGlRep_tensV {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (hE : IsGlRep E) :
    IsGlRep (tensV E) := by sorry
