-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_eps_bound
-- name    : ReciprocityTheory.ChartRestriction.G.I2.eps_bound
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:28:43.950828+00:00
-- url     : https://prove2.me/theorems/e2a5c386-31a4-4434-b0d1-71eda1dc5d41
-- title:
--   I2: eps bound
-- statement:
--   The I2 construction uses the eps bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/OneAddPowSubOneLe.lean#L104-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/OneAddPowSubOneLe.lean#L104-L126

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_OneAddPowSubOneLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2

theorem ReciprocityTheory.ChartRestriction.G.I2.eps_bound (g d : ℕ) (t K : ℝ) (h : g * Real.log 2 + 2 * d + 3 + K ≤ t) :
    7 * 2 ^ g * (4.3 : ℝ) ^ d * Real.exp (-t) ≤ Real.exp (-K) := by sorry
