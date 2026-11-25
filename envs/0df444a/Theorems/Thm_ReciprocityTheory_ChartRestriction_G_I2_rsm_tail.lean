-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_rsm_tail
-- name    : ReciprocityTheory.ChartRestriction.G.I2.rsm_tail
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:30:01.443527+00:00
-- url     : https://prove2.me/theorems/aafcb6a0-8f45-56ba-a924-e098e249ace2
-- title:
--   I2: rsm tail
-- statement:
--   The I2 construction uses the rsm tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/RSubMean.lean#L53-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/RSubMean.lean#L53-L101

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RSubMean
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Metric Set

theorem ReciprocityTheory.ChartRestriction.G.I2.rsm_tail (N : ℕ) (hN : 1 ≤ N) :
    ∫ y in Ioi (0 : ℝ), y ^ (2 * N - 1) *
        (Set.indicator (Ioi (Real.sqrt (2 * N))) (fun y => Real.exp (-y ^ 2)) y)
      ≤ (1 / 2) * ∫ y in Ioi (0 : ℝ), y ^ (2 * N - 1) * Real.exp (-y ^ 2) := by sorry
