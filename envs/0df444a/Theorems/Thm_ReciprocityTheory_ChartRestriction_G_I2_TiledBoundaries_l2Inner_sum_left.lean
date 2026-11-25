-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_l2Inner_sum_left
-- name    : ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.l2Inner_sum_left
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:04:20.158658+00:00
-- url     : https://prove2.me/theorems/646feaeb-e25f-42e5-aabd-314db9b53620
-- title:
--   Tiled Boundaries: l2 Inner sum left
-- statement:
--   The Tiled Boundaries construction uses the l2 Inner sum left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TiledBoundaries/PointwiseNormSqPullbackTensorEqProd.lean#L128-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TiledBoundaries/PointwiseNormSqPullbackTensorEqProd.lean#L128-L145

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

theorem ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.l2Inner_sum_left (hI : StepI) (X : PT E) (q : ℕ) {n : ℕ} {ι : Type} (t : Finset ι) (g : ι → ℂ)
    (F : ι → (Fin n → Vsp X.dim) → ℂ) (G : (Fin n → Vsp X.dim) → ℂ) (hF : ∀ j, Continuous (F j))
    (hG : Continuous G) :
    X.l2ip q (fun v => ∑ j ∈ t, g j * F j v) G = ∑ j ∈ t, g j * X.l2ip q (F j) G := by sorry
