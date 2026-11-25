-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_tof_shell_term
-- name    : ReciprocityTheory.ChartRestriction.G.I2.tof_shell_term
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:17:04.672942+00:00
-- url     : https://prove2.me/theorems/b9d9fa35-3489-4a5c-b7df-e324f6f8f141
-- title:
--   I2: tof shell term
-- statement:
--   The I2 construction uses the tof shell term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TofFinrankIRLe.lean#L11-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TofFinrankIRLe.lean#L11-L77

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

theorem ReciprocityTheory.ChartRestriction.G.I2.tof_shell_term (d k : ℕ) (hd : 2 ≤ d) :
    (3 * ((k : ℝ) + 1)) ^ d * Real.exp (-(Real.pi / 2) * (k : ℝ) ^ 2) ≤
      (3 * (d : ℝ)) ^ d * (Real.exp (-1) * Real.exp (1 - Real.pi / 2) ^ k) := by sorry
