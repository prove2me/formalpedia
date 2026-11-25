-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_sum_perm_succ
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.sum_perm_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:02:38.749902+00:00
-- url     : https://prove2.me/theorems/41b788cb-29ac-40a1-b5e3-7654183e9c48
-- title:
--   Capelli: sum perm succ
-- statement:
--   The Capelli construction uses the sum perm succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/BasicCycleRangeLastCastSucc.lean#L44-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/BasicCycleRangeLastCastSucc.lean#L44-L47

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_CapelliCentralStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_BasicCycleRangeLastCastSucc
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

theorem ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.sum_perm_succ {M : Type*} [AddCommMonoid M] {p : ℕ} (F : Equiv.Perm (Fin (p + 1)) → M) :
    ∑ σ, F σ = ∑ i, ∑ τ, F (permIns i τ) := by sorry
