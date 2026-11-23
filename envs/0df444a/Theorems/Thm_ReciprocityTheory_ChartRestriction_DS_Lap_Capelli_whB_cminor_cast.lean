-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_whB_cminor_cast
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.whB_cminor_cast
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:02:35.892793+00:00
-- url     : https://prove2.me/theorems/e3c37401-4c30-4167-b186-217262cde45f
-- title:
--   Capelli: wh B cminor cast
-- statement:
--   The Capelli construction uses the wh B cminor cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/CapelliWhittakerZero.lean#L70-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/CapelliWhittakerZero.lean#L70-L73

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowCol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_CapelliWhittakerZero
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
variable {M R : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup R] [Module ℂ R]

theorem ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.whB_cminor_cast {N : ℕ} [NeZero N] (E : Fin N → Fin N → Module.End ℂ M) {s t q s' t' q' : ℕ}
    (hq : q = q') (hs : s = s') (ht : t = t') (y : ℂ) :
    cminor E (whB_seg N s q) (whB_seg N t q) y = cminor E (whB_seg N s' q') (whB_seg N t' q') y := by sorry
