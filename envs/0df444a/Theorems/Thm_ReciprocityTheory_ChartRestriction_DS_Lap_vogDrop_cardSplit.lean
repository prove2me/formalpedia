-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_vogDrop_cardSplit
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.vogDrop_cardSplit
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:43:05.404076+00:00
-- url     : https://prove2.me/theorems/4ea23ca9-a03b-44ad-805b-e90f3639ddbb
-- title:
--   Lap: vog Drop card Split
-- statement:
--   The Lap construction uses the vog Drop card Split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/SpectralGap/VogDrop.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/SpectralGap/VogDrop.lean#L11-L16

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

theorem ReciprocityTheory.ChartRestriction.DS.Lap.vogDrop_cardSplit {n : ℕ} (p : Fin n → Prop) (q : Fin n → Prop) [DecidablePred p] [DecidablePred q] :
    ((univ.filter fun x => p x ∧ q x).card : ℝ) + ((univ.filter fun x => p x ∧ ¬ q x).card : ℝ)
      = ((univ.filter p).card : ℝ) := by sorry
