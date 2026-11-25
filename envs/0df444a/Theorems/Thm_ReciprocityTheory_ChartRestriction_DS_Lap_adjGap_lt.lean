-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_adjGap_lt
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.adjGap_lt
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:42:45.611027+00:00
-- url     : https://prove2.me/theorems/4867f846-21ec-4138-adb3-c65dd5d8214e
-- title:
--   Lap: adj Gap lt
-- statement:
--   The Lap construction uses the adj Gap lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/InterlacingWalks/AdjGap.lean#L23-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/InterlacingWalks/AdjGap.lean#L23-L40

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_LowerStepStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_AdjGap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap
open ReciprocityTheory.ChartRestriction.DS

theorem ReciprocityTheory.ChartRestriction.DS.Lap.adjGap_lt {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ) (hs : StrictAnti lam)
    (hadj : ∀ (a : Fin n) (ha : a.val + 1 < n), ε a ≠ ε ⟨a.val + 1, ha⟩ →
      h ≤ lam a - lam ⟨a.val + 1, ha⟩)
    (a b : Fin n) (hab : a.val < b.val) (hne : ε a ≠ ε b) : h ≤ lam a - lam b := by sorry
