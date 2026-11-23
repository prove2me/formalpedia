-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_rsm_finrank
-- name    : ReciprocityTheory.ChartRestriction.G.I2.rsm_finrank
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:23:49.701009+00:00
-- url     : https://prove2.me/theorems/94f52309-5509-4910-a68e-549468043468
-- title:
--   I2: rsm finrank
-- statement:
--   The I2 construction uses the rsm finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/RSubMean.lean#L30-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/RSubMean.lean#L30-L36

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

theorem ReciprocityTheory.ChartRestriction.G.I2.rsm_finrank (N : ℕ) : Module.finrank ℝ (EuclideanSpace ℂ (Fin N)) = 2 * N := by sorry
