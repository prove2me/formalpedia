-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_tof_span_condition
-- name    : ReciprocityTheory.ChartRestriction.G.I2.tof_span_condition
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T15:07:48.121285+00:00
-- url     : https://prove2.me/theorems/5dd0a536-a95f-4284-8d3b-618a87acd7d8
-- title:
--   I2: tof span condition
-- statement:
--   The I2 construction uses the tof span condition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TofSpanCondition.lean#L68-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TofSpanCondition.lean#L68-L144

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

theorem ReciprocityTheory.ChartRestriction.G.I2.tof_span_condition [IsCMField E] {X : PT E} (I : Submodule ℤ (Vsp X.dim)) (r1 : ℕ) (hr1 : 2 ≤ r1)
    (a yb : Fin X.r → Vsp X.dim) (hyb : ∀ j, yb j ∈ X.L)
    (hgen : ∀ x ∈ X.L, ∃ c : Fin X.r → 𝓞 E, ∃ y ∈ X.L,
      x = ∑ j, act (c j) (((r1 : ℂ) ^ 2) • a j) + (r1 : ℂ) • y) :
    Submodule.span ℝ {w | ∃ j, ∃ α : 𝓞 E,
      IsU I (act α (((r1 : ℂ) ^ 2) • a j - ((r1 : ℂ) ^ 2) • yb j)) w} = IR I := by sorry
