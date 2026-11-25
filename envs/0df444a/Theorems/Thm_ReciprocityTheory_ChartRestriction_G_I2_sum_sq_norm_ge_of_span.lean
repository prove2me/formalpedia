-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_sum_sq_norm_ge_of_span
-- name    : ReciprocityTheory.ChartRestriction.G.I2.sum_sq_norm_ge_of_span
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:51:16.02736+00:00
-- url     : https://prove2.me/theorems/ef173212-0cb5-45c9-8178-8f469a9ee0e9
-- title:
--   I2: sum sq norm ge of span
-- statement:
--   The I2 construction uses the sum sq norm ge of span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitV.lean#L32-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitV.lean#L32-L159

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitVB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitVC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
open scoped InnerProductSpace
noncomputable section
variable {E : Type} [Field E] [NumberField E]

theorem ReciprocityTheory.ChartRestriction.G.I2.sum_sq_norm_ge_of_span [IsCMField E] (X : PT E) (I : Submodule ℤ (Vsp X.dim)) (hle : I ≤ X.L)
    (hst : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I) {ξ : Vsp X.dim} (hξ : ξ ∈ I) (hξ0 : ξ ≠ 0)
    (k : ℕ) (x u : Fin k → Vsp X.dim) (hxu : ∀ j, x j ∈ X.L ∧ IsU I (x j) (u j))
    (hspan : Submodule.span ℝ {w | ∃ j, ∃ α : 𝓞 E, IsU I (act α (x j)) w} = IR I) :
    2 * PT.f E / (PT.rd E ^ 2 * ‖ξ‖ ^ 2) ≤ ∑ j, ‖u j‖ ^ 2 / 2 := by sorry
