-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_tof_shell_sum
-- name    : ReciprocityTheory.ChartRestriction.G.I2.tof_shell_sum
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:17:31.929598+00:00
-- url     : https://prove2.me/theorems/73530c31-fd81-4a0f-a004-a97f8c39b35c
-- title:
--   I2: tof shell sum
-- statement:
--   The I2 construction uses the tof shell sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TofFinrankIRLe.lean#L79-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TofFinrankIRLe.lean#L79-L112

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TofSpanCondition
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TofFinrankIRLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]

theorem ReciprocityTheory.ChartRestriction.G.I2.tof_shell_sum (d K : ℕ) (hd : 2 ≤ d) :
    ∑ k ∈ Finset.range K, (3 * ((k : ℝ) + 1)) ^ d * Real.exp (-(Real.pi / 2) * (k : ℝ) ^ 2) ≤
      2 * (3 * (d : ℝ)) ^ d := by sorry
