-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_lam_gap
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.lam_gap
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:43:07.461013+00:00
-- url     : https://prove2.me/theorems/4f0d495d-ae51-40ea-8f6f-83a7fc1bd988
-- title:
--   Lap: lam gap
-- statement:
--   The Lap construction uses the lam gap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/InterlacingWalks/InterlacesULt.lean#L72-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/InterlacingWalks/InterlacesULt.lean#L72-L85

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_LowerStepStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_AdjGap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_InterlacesULt
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

theorem ReciprocityTheory.ChartRestriction.DS.Lap.lam_gap {k r : ℕ} {v : Fin (k - 1) → ℝ} {b : Fin (2 * r + 2) → ℝ} {h : ℝ} (hk : 1 ≤ k)
    (hG : LowGaps r b h) (a : Fin (2 * r + k + 1)) (ha : a.val + 1 < 2 * r + k + 1)
    (hka : k - 1 ≤ a.val) :
    h ≤ parLam k r v b a - parLam k r v b ⟨a.val + 1, ha⟩ := by sorry
