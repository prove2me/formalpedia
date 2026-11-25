-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_lint_scl
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.J2.lint_scl
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:47:33.856027+00:00
-- url     : https://prove2.me/theorems/e38bca15-4f09-4fe1-9acb-9a9ab6a0922d
-- title:
--   J2: lint scl
-- statement:
--   The J2 construction uses the lint scl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/VolumeUnivFinZero.lean#L157-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/VolumeUnivFinZero.lean#L157-L166

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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.J2.lint_scl {p m : ℕ} {G : Xp p m → ℝ≥0∞} (hG : Measurable G) {t : ℝ} (ht : 0 < t) :
    ∫⁻ x, G x = ENNReal.ofReal (t ^ (4 * p + 2 * m + 2)) * ∫⁻ x, G (sclL p m t x) := by sorry
