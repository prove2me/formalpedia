-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_num_bound
-- name    : ReciprocityTheory.ChartRestriction.G.I2.num_bound
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:29:36.377232+00:00
-- url     : https://prove2.me/theorems/2bfa7bc0-55ae-4977-ba9d-c6c815315387
-- title:
--   I2: num bound
-- statement:
--   The I2 construction uses the num bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/OneAddPowSubOneLe.lean#L67-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/OneAddPowSubOneLe.lean#L67-L102

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

theorem ReciprocityTheory.ChartRestriction.G.I2.num_bound (r D : ℕ) (hr : 1 ≤ r) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε : ε ≤ Real.exp (-((D + 1) * (r * Real.log r + 3 * r + 3)))) :
    2 * D * (4 * r) ^ D * Real.exp ((r / 2 + 1) * D) * ε ≤ 1 := by sorry
