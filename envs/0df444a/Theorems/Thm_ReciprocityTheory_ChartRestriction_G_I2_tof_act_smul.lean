-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_tof_act_smul
-- name    : ReciprocityTheory.ChartRestriction.G.I2.tof_act_smul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:09:55.331092+00:00
-- url     : https://prove2.me/theorems/58e7dc3e-8c65-40cb-b2ae-8524dd60c34e
-- title:
--   I2: tof act smul
-- statement:
--   The I2 construction uses the tof act smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TofSpanCondition.lean#L37-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TofSpanCondition.lean#L37-L41

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SupRatioLeOfPhaseZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TofSpanCondition
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim

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

theorem ReciprocityTheory.ChartRestriction.G.I2.tof_act_smul {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) (c : ℂ) (v : Vsp dim) :
    act α (c • v) = c • act α v := by sorry
