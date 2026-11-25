-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_lowPt_sub
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.lowPt_sub
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:43:17.812427+00:00
-- url     : https://prove2.me/theorems/9326b308-049f-44cd-9643-1e63557fdbf6
-- title:
--   Lap: low Pt sub
-- statement:
--   The Lap construction uses the low Pt sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/InterlacingWalks/InterlacesULt.lean#L144-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/InterlacingWalks/InterlacesULt.lean#L144-L157

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

theorem ReciprocityTheory.ChartRestriction.DS.Lap.lowPt_sub {k r : ℕ} (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ)
    (i : ℕ) (hin : i < 2 * r + k + 1) (y : ℝ) :
    lowPt k r u v b i y - Pi.single (⟨i, hin⟩ : Fin (2 * r + k + 1)) (1 : ℝ) =
      lowPt k r u v b i (y - 1) := by sorry
