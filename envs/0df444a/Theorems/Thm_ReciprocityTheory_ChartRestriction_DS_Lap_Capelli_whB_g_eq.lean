-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_whB_g_eq
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.whB_g_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:02:37.63023+00:00
-- url     : https://prove2.me/theorems/7540b966-9f4b-4f5e-ae06-46919f74f4b5
-- title:
--   Capelli: wh B g eq
-- statement:
--   The Capelli construction uses the wh B g eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/CapelliWhittakerZero.lean#L78-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/CapelliWhittakerZero.lean#L78-L90

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

theorem ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.whB_g_eq {k r : ℕ} (ψ : Fin (k + 2 * r + 1) → Fin (k + 2 * r + 1) → ℂ) {a b0 : Fin (k + 2 * r + 1)}
    (h : IsSimplePair k r a b0) : whB_g k r ψ a = ψ a b0 := by sorry
