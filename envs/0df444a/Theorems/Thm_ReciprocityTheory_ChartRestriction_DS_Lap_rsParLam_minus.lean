-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_rsParLam_minus
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.rsParLam_minus
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:46:59.177307+00:00
-- url     : https://prove2.me/theorems/d3b40f96-4380-523f-8057-f63473532221
-- title:
--   Lap: rs Par Lam minus
-- statement:
--   The Lap construction uses the rs Par Lam minus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/InterlacingWalks/RsParLamMinus.lean#L120-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/InterlacingWalks/RsParLamMinus.lean#L120-L125

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

theorem ReciprocityTheory.ChartRestriction.DS.Lap.rsParLam_minus (k r : ℕ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ)
    (a : Fin (2 * r + k + 1)) (ha : k - 1 ≤ a.val) :
    parLam k r v b a = -rsExt b (a.val - (k - 1)) := by sorry
