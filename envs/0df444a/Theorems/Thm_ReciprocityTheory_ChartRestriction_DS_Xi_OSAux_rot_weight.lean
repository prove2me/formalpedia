-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_rot_weight
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.rot_weight
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:47:50.255649+00:00
-- url     : https://prove2.me/theorems/1eccb964-8d89-45ca-9e02-18d2f7ad2c5e
-- title:
--   OSAux: rot weight
-- statement:
--   The OSAux construction uses the rot weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/RhoMulStar.lean#L120-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/RhoMulStar.lean#L120-L196

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RhoMulStar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.OSAux

theorem ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.rot_weight (hS : SUB) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : ℂ) (c₀ : ℝ),
      ∫⁻ t in Icc (1 : ℝ) 2, ENNReal.ofReal ((1 + |2 * (rho t * X).im + c₀|) ^ (-δ)) ≤
        ENNReal.ofReal (C * (1 + |c₀|) ^ (-δ / 4) * (1 + ‖X‖) ^ (-δ / 4)) := by sorry
