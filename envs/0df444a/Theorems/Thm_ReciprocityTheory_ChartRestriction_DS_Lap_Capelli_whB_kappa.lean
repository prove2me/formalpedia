-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_whB_kappa
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.whB_kappa
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:43:34.54086+00:00
-- url     : https://prove2.me/theorems/5da0f887-2c20-5beb-9357-ab7cbaca8ae5
-- title:
--   Capelli: wh B kappa
-- statement:
--   The Capelli construction uses the wh B kappa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/CapelliWhittakerZero.lean#L96-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/CapelliWhittakerZero.lean#L96-L126

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

theorem ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.whB_kappa (k r : ℕ) (hr : 0 < r) (ψ : Fin (k + 2 * r + 1) → Fin (k + 2 * r + 1) → ℂ) :
    kappa k r ψ = (∏ j ∈ range r, whB_g k r ψ (whB_c (k + 2 * r + 1) (k + r + j))) *
      ((∏ i ∈ range (r - 1), whB_g k r ψ (whB_c (k + 2 * r + 1) (0 + i))) *
        whB_g k r ψ (whB_c (k + 2 * r + 1) (r - 1))) := by sorry
