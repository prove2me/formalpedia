-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_vogDrop_rhoSum
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.vogDrop_rhoSum
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:42:46.546103+00:00
-- url     : https://prove2.me/theorems/962861e3-2ad1-4a87-854b-4ab2191f1270
-- title:
--   Lap: vog Drop rho Sum
-- statement:
--   The Lap construction uses the vog Drop rho Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/SpectralGap/VogDrop.lean#L18-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/SpectralGap/VogDrop.lean#L18-L32

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

theorem ReciprocityTheory.ChartRestriction.DS.Lap.vogDrop_rhoSum {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    rhoC ε a + rhoN ε a = ((n : ℝ) - 1 - 2 * (a : ℕ)) / 2 := by sorry
