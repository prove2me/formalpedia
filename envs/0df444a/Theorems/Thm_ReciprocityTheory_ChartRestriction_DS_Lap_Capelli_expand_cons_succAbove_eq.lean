-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_expand_cons_succAbove_eq
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.expand_cons_succAbove_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:02:38.880189+00:00
-- url     : https://prove2.me/theorems/a52a9c11-bf79-4b0f-9aae-b9b453aa5884
-- title:
--   Capelli: expand cons succ Above eq
-- statement:
--   The Capelli construction uses the expand cons succ Above eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/Expand.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/Expand.lean#L13-L18

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

theorem ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.expand_cons_succAbove_eq (c : Fin (m + 1)) :
    (Fin.cons c c.succAbove : Fin (m + 1) → Fin (m + 1)) = id ∘ ⇑(Fin.cycleRange c).symm := by sorry
