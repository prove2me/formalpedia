-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_adjGap_exists_change
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.adjGap_exists_change
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:46:23.752254+00:00
-- url     : https://prove2.me/theorems/c41db7e4-e053-5f0c-8bd8-1fd934d97d35
-- title:
--   Lap: adj Gap exists change
-- statement:
--   The Lap construction uses the adj Gap exists change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/InterlacingWalks/AdjGap.lean#L7-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/InterlacingWalks/AdjGap.lean#L7-L21

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

theorem ReciprocityTheory.ChartRestriction.DS.Lap.adjGap_exists_change (f : ℕ → Bool) :
    ∀ d a : ℕ, f a ≠ f (a + d) → ∃ c, a ≤ c ∧ c < a + d ∧ f c ≠ f (c + 1) := by sorry
