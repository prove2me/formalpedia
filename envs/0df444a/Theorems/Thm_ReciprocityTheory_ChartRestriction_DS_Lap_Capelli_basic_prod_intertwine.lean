-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_basic_prod_intertwine
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.basic_prod_intertwine
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:42:36.448323+00:00
-- url     : https://prove2.me/theorems/5d322093-70bd-4ff4-ad4d-e7389aa9b3e7
-- title:
--   Capelli: basic prod intertwine
-- statement:
--   The Capelli construction uses the basic prod intertwine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/BasicCycleRangeLastCastSucc.lean#L139-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/BasicCycleRangeLastCastSucc.lean#L139-L146

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

theorem ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.basic_prod_intertwine {M R' : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup R'] [Module ℂ R']
    (l : M →ₗ[ℂ] R') : ∀ {m : ℕ} (f : Fin m → Module.End ℂ M) (g : Fin m → Module.End ℂ R'),
    (∀ j, l ∘ₗ f j = g j ∘ₗ l) → l ∘ₗ (List.ofFn f).prod = (List.ofFn g).prod ∘ₗ l
  := by sorry
