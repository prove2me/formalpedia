-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_rsPt_succ
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.rsPt_succ
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:42:54.8032+00:00
-- url     : https://prove2.me/theorems/129cba4d-48d2-4dcd-89c6-1b8c00aaa682
-- title:
--   Lap: rs Pt succ
-- statement:
--   The Lap construction uses the rs Pt succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/InterlacingWalks/RsParLamMinus.lean#L40-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/InterlacingWalks/RsParLamMinus.lean#L40-L47

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

theorem ReciprocityTheory.ChartRestriction.DS.Lap.rsPt_succ (k r : ℕ) (u : Fin k → ℝ) (b : Fin (2 * r + 2) → ℝ) (t j m : ℕ)
    (hk : 1 ≤ k) (hj : 1 ≤ j) (hj2 : j ≤ 2 * r + 1) :
    rsPt k r u b t j (m + 1) =
      rsPt k r u b t j m + Pi.single (⟨j + k - 1, by omega⟩ : Fin (2 * r + k + 1)) 1 := by sorry
