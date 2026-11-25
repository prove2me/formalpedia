-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_lemS_finrank
-- name    : ReciprocityTheory.ChartRestriction.G.I2.lemS_finrank
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:29:12.563495+00:00
-- url     : https://prove2.me/theorems/7e1dacfb-e0cc-4856-aed9-c1a452d58688
-- title:
--   I2: lem S finrank
-- statement:
--   The I2 construction uses the lem S finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/LemmaSB.lean#L11-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/LemmaSB.lean#L11-L20

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RSubMean
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaSB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex Metric
noncomputable section
variable {ι : Type} [Fintype ι]

theorem ReciprocityTheory.ChartRestriction.G.I2.lemS_finrank : Module.finrank ℝ (EuclideanSpace ℂ ι) = 2 * Fintype.card ι := by sorry
