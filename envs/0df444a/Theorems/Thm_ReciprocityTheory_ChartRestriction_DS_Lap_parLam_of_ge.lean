-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_parLam_of_ge
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.parLam_of_ge
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:03:17.621256+00:00
-- url     : https://prove2.me/theorems/19431c2f-a635-4dba-970a-4f25fff6f5a3
-- title:
--   Lap: par Lam of ge
-- statement:
--   The Lap construction uses the par Lam of ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/InterlacingWalks/InterlacesULt.lean#L52-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/InterlacingWalks/InterlacesULt.lean#L52-L56

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

theorem ReciprocityTheory.ChartRestriction.DS.Lap.parLam_of_ge {k r : ℕ} {v : Fin (k - 1) → ℝ} {b : Fin (2 * r + 2) → ℝ} (a : ℕ)
    (ha : a < 2 * r + k + 1) (h : k - 1 ≤ a) :
    parLam k r v b ⟨a, ha⟩ = -b ⟨a - (k - 1), by omega⟩ := by sorry
