-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_walkPar_add
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.walkPar_add
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:45:43.923051+00:00
-- url     : https://prove2.me/theorems/94ad30da-5fac-5328-9b9b-b92821fcc147
-- title:
--   Lap: walk Par add
-- statement:
--   The Lap construction uses the walk Par add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/InterlacingWalks/InterlacesULt.lean#L127-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/InterlacingWalks/InterlacesULt.lean#L127-L142

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

theorem ReciprocityTheory.ChartRestriction.DS.Lap.walkPar_add {k r : ℕ} (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ)
    (i : ℕ) (hi : i < k) (hin : i < 2 * r + k + 1) (c : ℝ) :
    walkPar k r u v b (i + 1) + c • Pi.single (⟨i, hin⟩ : Fin (2 * r + k + 1)) (1 : ℝ) =
      lowPt k r u v b i (u ⟨i, hi⟩ - 1 / 2 + c) := by sorry
