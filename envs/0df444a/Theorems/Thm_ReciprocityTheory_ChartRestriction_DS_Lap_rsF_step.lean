-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_rsF_step
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.rsF_step
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:45:51.928992+00:00
-- url     : https://prove2.me/theorems/2cfce0d1-0af8-5508-aadd-2b27daf89376
-- title:
--   Lap: rs F step
-- statement:
--   The Lap construction uses the rs F step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/InterlacingWalks/RsParLamMinus.lean#L91-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/InterlacingWalks/RsParLamMinus.lean#L91-L118

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

theorem ReciprocityTheory.ChartRestriction.DS.Lap.rsF_step (k r : ℕ) (U B : ℕ → ℝ) (h : ℝ) (t j m x : ℕ) (hk : 1 ≤ k) (hm : m ≤ j * t)
    (hBlt : ∀ q, q + 1 < 2 * r + 2 → B q < B (q + 1))
    (hBgap : ∀ q, q + 1 < 2 * r + 2 → h ≤ B (q + 1) - B q)
    (hUlt : ∀ x, x + 1 < k → U (x + 1) < U x) (hUhalf : -B 0 ≤ U (k - 1) - 1 / 2)
    (hx : x + 1 < 2 * r + k + 1) :
    rsF k U B t j m (x + 1) < rsF k U B t j m x ∧
      (k - 1 ≤ x → h ≤ rsF k U B t j m x - rsF k U B t j m (x + 1)) := by sorry
