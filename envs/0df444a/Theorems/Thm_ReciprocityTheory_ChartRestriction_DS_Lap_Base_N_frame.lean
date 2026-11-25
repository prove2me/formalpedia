-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_frame
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.frame
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:41:17.034256+00:00
-- url     : https://prove2.me/theorems/f57fd138-6a3b-53dd-8adc-47d9da51b94a
-- title:
--   N: frame
-- statement:
--   The N construction uses the frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/LaplaceFoundations/OneParameterSubgroups/ExistsCyclic.lean#L135-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/LaplaceFoundations/OneParameterSubgroups/ExistsCyclic.lean#L135-L219

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

theorem ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.frame (r : ℕ) (x : Fin (2 * r + 1) → ℝ) (hx : StrictAnti x) :
    ∃ (e f : Fin r → Fin (2 * r + 1) → ℝ) (z : Fin (2 * r + 1) → ℝ),
      (∀ a b, formV (e a) (e b) = 0) ∧ (∀ a b, formV (f a) (f b) = 0) ∧
      (∀ a b, formV (f a) (e b) = if a = b then 1 else 0) ∧
      (∀ a, formV (e a) z = 0) ∧ (∀ a, formV (f a) z = 0) ∧ formV z z = -1 ∧
      (∀ a s, x s * e a s = if h : a.val + 1 < r then e ⟨a.val + 1, h⟩ s else z s) := by sorry
