-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_rsPt_zero
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.rsPt_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:45:25.741055+00:00
-- url     : https://prove2.me/theorems/33944092-7d23-5500-ac44-130964a051ac
-- title:
--   Lap: rs Pt zero
-- statement:
--   The Lap construction uses the rs Pt zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/InterlacingWalks/RsParLamMinus.lean#L26-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/InterlacingWalks/RsParLamMinus.lean#L26-L31

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

theorem ReciprocityTheory.ChartRestriction.DS.Lap.rsPt_zero (k r : ℕ) (u : Fin k → ℝ) (b : Fin (2 * r + 2) → ℝ) (t j : ℕ) :
    rsPt k r u b t j 0 = raisePar k r u b t j := by sorry
