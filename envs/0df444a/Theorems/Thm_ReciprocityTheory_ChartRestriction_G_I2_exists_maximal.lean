-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_exists_maximal
-- name    : ReciprocityTheory.ChartRestriction.G.I2.exists_maximal
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:51:27.983724+00:00
-- url     : https://prove2.me/theorems/e1de9820-c1c2-4cf7-b18b-94ba804e021a
-- title:
--   I2: exists maximal
-- statement:
--   The I2 construction uses the exists maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ExistsMaximal.lean#L196-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ExistsMaximal.lean#L196-L222

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ExistsMaximal
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
variable [IsCMField E]

theorem ReciprocityTheory.ChartRestriction.G.I2.exists_maximal (X : PT E) {n : ℕ} (ω : Fin n → 𝓞 E) {Ω th : ℝ} (hΩ : 0 < Ω)
    (hth : 0 < th) (hΩth : Ω * th ^ 2 ≤ 1) (hω : ∀ j (σ : E →+* ℂ), ‖σ (ω j)‖ ≤ Ω)
    (hsp : ∀ α : 𝓞 E, (α : E) ∈ Submodule.span ℚ (Set.range fun j => (ω j : E))) :
    ∃ I, Good X (1 / (Ω * th)) I ∧ ∀ x ∈ X.L, x ∉ I → th ≤ Metric.infDist x (IR I) := by sorry
