-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_tof_re_inner_negI
-- name    : ReciprocityTheory.ChartRestriction.G.I2.tof_re_inner_negI
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:10:42.8526+00:00
-- url     : https://prove2.me/theorems/54649f10-8846-4673-8c24-653ab16b8f54
-- title:
--   I2: tof re inner neg I
-- statement:
--   The I2 construction uses the tof re inner neg I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TofSpanCondition.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TofSpanCondition.lean#L16-L21

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SupRatioLeOfPhaseZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TofSpanCondition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex NumberField
noncomputable section
variable {E : Type} [Field E] [NumberField E]

theorem ReciprocityTheory.ChartRestriction.G.I2.tof_re_inner_negI {ι : Type} [Fintype ι] (a x : EuclideanSpace ℂ ι) :
    inner ℝ a ((-Complex.I) • x) = (Hf x a).im := by sorry
