-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_vogDrop
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.vogDrop
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:08:38.877207+00:00
-- url     : https://prove2.me/theorems/8619c263-406c-4513-b05f-8dbae847c0aa
-- title:
--   Lap: vog Drop
-- statement:
--   The Lap construction uses the vog Drop property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/SpectralGap/VogDrop.lean#L34-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/SpectralGap/VogDrop.lean#L34-L54

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_SpectralGap_CasOnLowStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_SpectralGap_VogDrop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap
open ReciprocityTheory.ChartRestriction.DS

theorem ReciprocityTheory.ChartRestriction.DS.Lap.vogDrop (n : ℕ) : VogDropStatement n := by sorry
