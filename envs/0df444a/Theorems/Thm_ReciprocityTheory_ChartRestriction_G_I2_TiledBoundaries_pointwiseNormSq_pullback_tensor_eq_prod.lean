-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_pointwiseNormSq_pullback_tensor_eq_prod
-- name    : ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.pointwiseNormSq_pullback_tensor_eq_prod
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:54:19.854771+00:00
-- url     : https://prove2.me/theorems/20bb3c31-d0cf-4dae-a43a-c4fbdc6bd2a3
-- title:
--   Tiled Boundaries: pointwise Norm Sq pullback tensor eq prod
-- statement:
--   The Tiled Boundaries construction uses the pointwise Norm Sq pullback tensor eq prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TiledBoundaries/PointwiseNormSqPullbackTensorEqProd.lean#L71-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TiledBoundaries/PointwiseNormSqPullbackTensorEqProd.lean#L71-L80

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_DimStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_PointwiseNormSqPullbackTensorEqProd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim

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

theorem ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.pointwiseNormSq_pullback_tensor_eq_prod (X : PT E) {q n : ℕ} {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (hπ : IsPi X q π)
    (s : (Fin 1 → Vsp X.dim) → ℂ) (v : Fin n → Vsp X.dim) :
    X.ptN2 q (s0 X π s) v = ∏ k, X.ptN2 1 s (fun _ => π (v k)) := by sorry
