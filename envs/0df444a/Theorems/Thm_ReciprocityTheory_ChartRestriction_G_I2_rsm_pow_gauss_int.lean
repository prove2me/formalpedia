-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_rsm_pow_gauss_int
-- name    : ReciprocityTheory.ChartRestriction.G.I2.rsm_pow_gauss_int
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:30:13.606015+00:00
-- url     : https://prove2.me/theorems/e30b6d30-aa67-4fa8-88bf-8abffa56a1bb
-- title:
--   I2: rsm pow gauss int
-- statement:
--   The I2 construction uses the rsm pow gauss int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/RSubMean.lean#L21-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/RSubMean.lean#L21-L28

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

theorem ReciprocityTheory.ChartRestriction.G.I2.rsm_pow_gauss_int (k : ℕ) :
    IntegrableOn (fun y : ℝ => y ^ k * Real.exp (-y ^ 2)) (Ioi 0) := by sorry
