-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_base_pt
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.J2.base_pt
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:47:48.719611+00:00
-- url     : https://prove2.me/theorems/fd8cf445-54f0-42fd-9d2d-ddfcfe6a78b1
-- title:
--   J2: base pt
-- statement:
--   The J2 construction uses the base pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/VolumeUnivFinZero.lean#L168-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/VolumeUnivFinZero.lean#L168-L230

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GaugeSplittingAlgebra
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_VolumeUnivFinZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Module
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.J2

theorem ReciprocityTheory.ChartRestriction.DS.Xi.J2.base_pt (m : ℕ) (v : ℝ) (hv : 0 < v) (x : Xp 0 m) :
    de x 0 ^ (-(s0N 0 m 0 + v)) ≤ 2 ^ (m + v / 2 : ℝ) *
      ((1 + ‖x.2.2.1‖ ^ 2) ^ (-(2 * (m + v / 2 : ℝ)) / 2) * (1 + ‖x.2.2.2‖ ^ 2) ^ (-(1 + v / 2) / 2)) := by sorry
