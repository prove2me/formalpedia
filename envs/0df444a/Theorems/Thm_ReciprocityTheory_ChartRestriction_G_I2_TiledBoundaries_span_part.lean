-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_span_part
-- name    : ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.span_part
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:09:45.425131+00:00
-- url     : https://prove2.me/theorems/5e9986e8-4c99-49c6-9721-8f3db619fa54
-- title:
--   Tiled Boundaries: span part
-- statement:
--   The Tiled Boundaries construction uses the span part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TiledBoundaries/NstatementOf.lean#L161-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TiledBoundaries/NstatementOf.lean#L161-L198

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_PointwiseNormSqPullbackTensorEqProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_NstatementOf
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

theorem ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.span_part (hI : StepI) (hPos : StepPos) (hKc : StepK) (hD : StepD) (X : PT E) {q n : ℕ}
    {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (hq : 1 ≤ q) (hπ : IsPi X q π) {s : (Fin 1 → Vsp X.dim) → ℂ}
    (hs : s ∈ X.Sec 1 1) (hs0 : s ≠ 0) {K : Finset (Fin n → Vsp X.dim)} (hK : IsReps X q n π K)
    (h1 : ∀ b ∈ K, X.U q b (s0 X π s) ∈ X.Sec q n)
    (h2 : ∀ b ∈ K, ∀ b' ∈ K, b ≠ b' → X.l2ip q (X.U q b (s0 X π s)) (X.U q b' (s0 X π s)) = 0)
    (h3 : ∀ b ∈ K, X.l2 q (X.U q b (s0 X π s)) = X.l2 1 s ^ n) :
    X.Sec q n ≤ Submodule.span ℂ ((fun b => X.U q b (s0 X π s)) '' (K : Set _)) := by sorry
