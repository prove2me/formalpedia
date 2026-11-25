-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_rsm_prod_int
-- name    : ReciprocityTheory.ChartRestriction.G.I2.rsm_prod_int
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:30:05.486506+00:00
-- url     : https://prove2.me/theorems/0f07a896-a1d3-4e53-a42e-76c05ca68c7d
-- title:
--   I2: rsm prod int
-- statement:
--   The I2 construction uses the rsm prod int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/RSubMean.lean#L244-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/RSubMean.lean#L244-L257

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

theorem ReciprocityTheory.ChartRestriction.G.I2.rsm_prod_int (N : ℕ) (F : EuclideanSpace ℂ (Fin N) → ℂ) (hF : Continuous F) (r : ℝ) :
    Integrable (fun p : EuclideanSpace ℂ (Fin N) × ℝ =>
        Real.exp (-‖p.1‖ ^ 2) * ‖F (circleMap 0 1 p.2 • p.1)‖ ^ 2)
      ((volume.restrict (closedBall 0 r)).prod (volume.restrict (Ioc 0 (2 * Real.pi)))) := by sorry
