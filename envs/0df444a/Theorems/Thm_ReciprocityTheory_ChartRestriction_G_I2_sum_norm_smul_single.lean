-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_sum_norm_smul_single
-- name    : ReciprocityTheory.ChartRestriction.G.I2.sum_norm_smul_single
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:30:23.849196+00:00
-- url     : https://prove2.me/theorems/2607260f-c9d7-43a9-aafd-e5efc148b3c8
-- title:
--   I2: sum norm smul single
-- statement:
--   The I2 construction uses the sum norm smul single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/RCauchy.lean#L8-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/RCauchy.lean#L8-L14

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RCauchy
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Metric

theorem ReciprocityTheory.ChartRestriction.G.I2.sum_norm_smul_single {N : ℕ} (a : Fin N) (w : ℂ) :
    ∑ i, ‖(w • (Pi.single a (1 : ℂ) : Fin N → ℂ)) i‖ = ‖w‖ := by sorry
