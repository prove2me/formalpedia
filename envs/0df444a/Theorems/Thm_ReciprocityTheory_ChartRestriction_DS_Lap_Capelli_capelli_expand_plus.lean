-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_capelli_expand_plus
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.capelli_expand_plus
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:59:22.182965+00:00
-- url     : https://prove2.me/theorems/949dc1ae-bae6-4713-8924-9302fad93e2e
-- title:
--   Capelli: capelli expand plus
-- statement:
--   The Capelli construction uses the capelli expand plus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/Expand.lean#L35-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/Expand.lean#L35-L58

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

theorem ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.capelli_expand_plus (hE : GlRelR E) (om : ℂ) (b c : Fin (m + 1)) :
    ∑ d : Fin (m + 1), ((-1 : ℂ) ^ ((d : ℕ) + (c : ℕ))) •
        (capEntry E om d b * cminor E d.succAbove c.succAbove (om - 1)) =
      if b = c then capelliC E om else 0 := by sorry
