-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_exists_cyclic
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.exists_cyclic
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:41:24.859745+00:00
-- url     : https://prove2.me/theorems/5563ebea-2b6d-4ac0-bee8-3112aa48c9db
-- title:
--   N: exists cyclic
-- statement:
--   The N construction uses the exists cyclic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/LaplaceFoundations/OneParameterSubgroups/ExistsCyclic.lean#L69-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/LaplaceFoundations/OneParameterSubgroups/ExistsCyclic.lean#L69-L108

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_LaplaceFoundations_OneParameterSubgroups_ExistsCyclic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Base ReciprocityTheory.ChartRestriction.DS.Lap.Base.N

theorem ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.exists_cyclic (r : ℕ) (x : Fin (2 * r + 1) → ℝ) (hx : StrictAnti x) :
    ∃ c : Fin (2 * r + 1) → ℝ, (∀ s, c s ≠ 0) ∧ ∀ i j : ℕ, i + j ≤ 2 * r →
      formV (fun s => x s ^ i * c s) (fun s => x s ^ j * c s) = if i + j = 2 * r then -1 else 0 := by sorry
