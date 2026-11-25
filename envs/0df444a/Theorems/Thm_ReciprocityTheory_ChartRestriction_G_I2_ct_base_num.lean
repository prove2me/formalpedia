-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_ct_base_num
-- name    : ReciprocityTheory.ChartRestriction.G.I2.ct_base_num
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:28:42.338859+00:00
-- url     : https://prove2.me/theorems/b802c20d-ad81-4f33-a8d6-2ee639b65f1f
-- title:
--   I2: ct base num
-- statement:
--   The I2 construction uses the ct base num property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColTorusB.lean#L49-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColTorusB.lean#L49-L82

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColTorusB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Real

theorem ReciprocityTheory.ChartRestriction.G.I2.ct_base_num (q c : ℕ) (hq : 1 ≤ q) {t0 : ℝ}
    (hC5 : 4 * (c : ℝ) * (7 + Real.log (q * c)) ≤ t0) :
    (6.5 * Real.exp 1.07 * Real.sqrt (q * (c + 1))) ^ c ≤ Real.exp (0.14 * t0) := by sorry
