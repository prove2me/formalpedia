-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_exists_perm_swap_succAbove
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.exists_perm_swap_succAbove
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:02:23.896579+00:00
-- url     : https://prove2.me/theorems/b3433c6c-9ef4-4585-8677-e600e45af5cc
-- title:
--   Capelli: exists perm swap succ Above
-- statement:
--   The Capelli construction uses the exists perm swap succ Above property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/RowColA.lean#L12-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/RowColA.lean#L12-L43

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowAnti
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_ProdOfFnUpdateEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowColA
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

theorem ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.exists_perm_swap_succAbove {p : ℕ} (i s : Fin (p + 1)) (h : i ≠ s) :
    ∃ π : Equiv.Perm (Fin p), ((Equiv.Perm.sign π : ℤˣ) : ℤ) = (-1) ^ ((i : ℕ) + (s : ℕ) + 1) ∧
      ∀ t, Equiv.swap i s (i.succAbove t) = s.succAbove (π t) := by sorry
