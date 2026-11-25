-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_ct_expo_num
-- name    : ReciprocityTheory.ChartRestriction.G.I2.ct_expo_num
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:28:32.180532+00:00
-- url     : https://prove2.me/theorems/43e092ef-29d2-5d81-8f7f-e4c30ab71a70
-- title:
--   I2: ct expo num
-- statement:
--   The I2 construction uses the ct expo num property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColTorusB.lean#L7-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColTorusB.lean#L7-L47

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

theorem ReciprocityTheory.ChartRestriction.G.I2.ct_expo_num (q c : ℕ) (hq : 1 ≤ q) {U y M1 r : ℝ} (hU : 0 ≤ U) (hy : 0 ≤ y)
    (hM : M1 ≤ q / 2) (hr0 : 0 ≤ r) (hr : r * (2 * π * U + 5 * Real.sqrt (q * (c + 1))) ≤ c)
    (ht : 28 * (c : ℝ) ≤ q * y ^ 2) :
    q * π * r ^ 2 / 2 + 2 * π * r * (U + q * y) - π * (q - M1) * y ^ 2 ≤
      1.07 * c - 1.33 * (q * y ^ 2) := by sorry
