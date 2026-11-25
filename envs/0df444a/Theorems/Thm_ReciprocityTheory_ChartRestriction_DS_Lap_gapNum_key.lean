-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_gapNum_key
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.gapNum_key
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:42:58.984471+00:00
-- url     : https://prove2.me/theorems/09c3cfe4-118d-4f9f-a535-e8b3b7048e01
-- title:
--   Lap: gap Num key
-- statement:
--   The Lap construction uses the gap Num key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/SpectralGap/GapNum.lean#L17-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/SpectralGap/GapNum.lean#L17-L31

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_SpectralGap_GapNum
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

theorem ReciprocityTheory.ChartRestriction.DS.Lap.gapNum_key (Q Nn T : ℝ) (hQ : 1 ≤ Q) (hN : 2 ≤ Nn) (hT : Nn + 5 ≤ T) :
    160 * Q ^ 2 * Nn ^ 2 ≤ 2 * (Nn + 2 * Q * T) ^ 3 := by sorry
