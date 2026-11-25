-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_cont_ip
-- name    : ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.cont_ip
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:52:20.609732+00:00
-- url     : https://prove2.me/theorems/e619d1d5-a3a7-4a7e-b75d-806d50a735dc
-- title:
--   Tiled Boundaries: cont ip
-- statement:
--   The Tiled Boundaries construction uses the cont ip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TiledBoundaries/PointwiseNormSqPullbackTensorEqProd.lean#L64-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TiledBoundaries/PointwiseNormSqPullbackTensorEqProd.lean#L64-L69

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_DimStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_PointwiseNormSqPullbackTensorEqProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
open ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]

theorem ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.cont_ip (q : ℕ) {n : ℕ} {ι : Type} [Fintype ι] {F G : (Fin n → EuclideanSpace ℂ ι) → ℂ}
    (hF : Continuous F) (hG : Continuous G) :
    Continuous (fun v => F v * (starRingEnd ℂ) (G v) *
      ((Real.exp (-(q * Real.pi) * (HC v v).re) : ℝ) : ℂ)) := by sorry
