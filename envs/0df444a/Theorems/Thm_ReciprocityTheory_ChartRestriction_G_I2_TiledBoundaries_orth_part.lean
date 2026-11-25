-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_orth_part
-- name    : ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.orth_part
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T15:10:05.851366+00:00
-- url     : https://prove2.me/theorems/605b49dc-d25a-4b18-af4d-3fbe4c4fa08b
-- title:
--   Tiled Boundaries: orth part
-- statement:
--   The Tiled Boundaries construction uses the orth part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TiledBoundaries/NstatementOf.lean#L70-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TiledBoundaries/NstatementOf.lean#L70-L159

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

theorem ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.orth_part (hT : StepT) (hDual : StepDual) (X : PT E) {q n : ℕ}
    {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (hq : 1 ≤ q) (hπ : IsPi X q π) {s : (Fin 1 → Vsp X.dim) → ℂ}
    (hs : s ∈ X.Sec 1 1) {K : Finset (Fin n → Vsp X.dim)} (hK : IsReps X q n π K)
    {b b' : Fin n → Vsp X.dim} (hb : b ∈ K) (hb' : b' ∈ K) (hne : b ≠ b') :
    X.l2ip q (X.U q b (s0 X π s)) (X.U q b' (s0 X π s)) = 0 := by sorry
