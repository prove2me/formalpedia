-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_tof_fg_div_eq_bot
-- name    : ReciprocityTheory.ChartRestriction.G.I2.tof_fg_div_eq_bot
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:09:47.426902+00:00
-- url     : https://prove2.me/theorems/f030a8a7-f2ea-4e28-bcd6-eaea59ed4f5f
-- title:
--   I2: tof fg div eq bot
-- statement:
--   The I2 construction uses the tof fg div eq bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TofSpanCondition.lean#L46-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TofSpanCondition.lean#L46-L66

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

theorem ReciprocityTheory.ChartRestriction.G.I2.tof_fg_div_eq_bot {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]
    (M : Submodule ℤ Q) (hM : M.FG)
    (r : ℕ) (hr : 2 ≤ r) (hdiv : ∀ m ∈ M, ∃ m' ∈ M, m = r • m') : M = ⊥ := by sorry
