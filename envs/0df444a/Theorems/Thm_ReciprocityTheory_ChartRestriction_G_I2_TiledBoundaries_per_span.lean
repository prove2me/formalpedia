-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_per_span
-- name    : ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.per_span
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:15:12.977334+00:00
-- url     : https://prove2.me/theorems/eb931f27-b70d-55a7-81f4-24ac8f7a3a25
-- title:
--   Tiled Boundaries: per span
-- statement:
--   The Tiled Boundaries construction uses the per span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TiledBoundaries/MemSpanBn.lean#L59-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TiledBoundaries/MemSpanBn.lean#L59-L65

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_PointwiseNormSqPullbackTensorEqProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_MemSpanBn
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
open ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory Complex Module
noncomputable section
variable {E : Type} [Field E] [NumberField E]

theorem ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.per_span (X : PT E) (n : ℕ) {F : Type} (g : (Fin n → Vsp X.dim) → F)
    (hper : ∀ γ : Fin n → Vsp X.dim, (∀ k, γ k ∈ X.L) → ∀ v, g (v + γ) = g v) :
    ∀ (γ : (Submodule.span ℤ (Set.range (Bn X n))).toAddSubgroup) (x), g (γ +ᵥ x) = g x := by sorry
