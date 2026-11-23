-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_capelli_expand_minus
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.capelli_expand_minus
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:46:58.324362+00:00
-- url     : https://prove2.me/theorems/c1a55764-b47b-4330-9edc-9fef769f21c4
-- title:
--   Capelli: capelli expand minus
-- statement:
--   The Capelli construction uses the capelli expand minus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/Expand.lean#L60-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/Expand.lean#L60-L83

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowCol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_Expand
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
variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {m : ℕ} (E : Fin (m + 1) → Fin (m + 1) → 𝒰)

theorem ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.capelli_expand_minus (hE : GlRelR E) (om : ℂ) (a c : Fin (m + 1)) :
    ∑ d : Fin (m + 1), ((-1 : ℂ) ^ ((d : ℕ) + (c : ℕ))) •
        (capEntry E (om - (m : ℂ)) a d * cminor E c.succAbove d.succAbove om) =
      if a = c then capelliC E om else 0 := by sorry
