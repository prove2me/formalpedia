-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_expand_sign_cycleRange_symm
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.expand_sign_cycleRange_symm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:02:46.600521+00:00
-- url     : https://prove2.me/theorems/174fd33d-c3bc-442f-a0d1-9ed3f00f8c6c
-- title:
--   Capelli: expand sign cycle Range symm
-- statement:
--   The Capelli construction uses the expand sign cycle Range symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/Expand.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/Expand.lean#L20-L24

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

theorem ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.expand_sign_cycleRange_symm (c : Fin (m + 1)) :
    (((Equiv.Perm.sign (Fin.cycleRange c).symm : ℤˣ) : ℤ) : ℂ) = (-1 : ℂ) ^ (c : ℕ) := by sorry
