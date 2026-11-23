-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_lowPt_lt
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.lowPt_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:03:11.869222+00:00
-- url     : https://prove2.me/theorems/45354918-bad6-4ff7-8b75-72950eb1a301
-- title:
--   Lap: low Pt lt
-- statement:
--   The Lap construction uses the low Pt lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/InterlacingWalks/InterlacesULt.lean#L107-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/InterlacingWalks/InterlacesULt.lean#L107-L115

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

theorem ReciprocityTheory.ChartRestriction.DS.Lap.lowPt_lt {k r : ℕ} {u : Fin k → ℝ} {v : Fin (k - 1) → ℝ} {b : Fin (2 * r + 2) → ℝ}
    (i : ℕ) (x : ℝ) (hi : i < k) (a : Fin (2 * r + k + 1)) (ha : a.val < i) :
    lowPt k r u v b i x a = u ⟨a.val, by omega⟩ - 1 / 2 := by sorry
