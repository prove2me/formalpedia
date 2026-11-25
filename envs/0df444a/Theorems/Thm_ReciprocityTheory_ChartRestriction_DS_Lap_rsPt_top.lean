-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_rsPt_top
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.rsPt_top
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:45:16.327726+00:00
-- url     : https://prove2.me/theorems/926b71db-862e-5557-8c79-5b242234b0b8
-- title:
--   Lap: rs Pt top
-- statement:
--   The Lap construction uses the rs Pt top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/InterlacingWalks/RsParLamMinus.lean#L33-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/InterlacingWalks/RsParLamMinus.lean#L33-L38

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_LowerStepStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_AdjGap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_RsParLamMinus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap
open ReciprocityTheory.ChartRestriction.DS

theorem ReciprocityTheory.ChartRestriction.DS.Lap.rsPt_top (k r : ℕ) (u : Fin k → ℝ) (b : Fin (2 * r + 2) → ℝ) (t j : ℕ) :
    rsPt k r u b t j (j * t) = raisePar k r u b t (j + 1) := by sorry
