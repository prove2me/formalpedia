-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_rsG_step
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.rsG_step
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:42:52.36084+00:00
-- url     : https://prove2.me/theorems/a1ac4d77-8328-41c0-a7fb-11c391c52429
-- title:
--   Lap: rs G step
-- statement:
--   The Lap construction uses the rs G step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/InterlacingWalks/RsParLamMinus.lean#L49-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/InterlacingWalks/RsParLamMinus.lean#L49-L76

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

theorem ReciprocityTheory.ChartRestriction.DS.Lap.rsG_step (B : ℕ → ℝ) (h : ℝ) (t j m q N : ℕ) (hm : m ≤ j * t)
    (hBlt : ∀ q, q + 1 < N → B q < B (q + 1)) (hBgap : ∀ q, q + 1 < N → h ≤ B (q + 1) - B q)
    (hq : q + 1 < N) :
    rsG B t j m (q + 1) < rsG B t j m q ∧ h ≤ rsG B t j m q - rsG B t j m (q + 1) := by sorry
