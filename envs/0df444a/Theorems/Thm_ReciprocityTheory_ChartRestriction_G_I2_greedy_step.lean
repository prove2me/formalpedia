-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_greedy_step
-- name    : ReciprocityTheory.ChartRestriction.G.I2.greedy_step
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:29:15.094051+00:00
-- url     : https://prove2.me/theorems/b43dff63-5bf1-4a05-87d1-971c8fc4aeff
-- title:
--   I2: greedy step
-- statement:
--   The I2 construction uses the greedy step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ExistsMaximal.lean#L23-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ExistsMaximal.lean#L23-L194

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

theorem ReciprocityTheory.ChartRestriction.G.I2.greedy_step (X : PT E) {n : ℕ} (ω : Fin n → 𝓞 E) {Ω th : ℝ} (hΩ : 0 < Ω) (hth : 0 < th)
    (hΩth : Ω * th ^ 2 ≤ 1) (hω : ∀ j (σ : E →+* ℂ), ‖σ (ω j)‖ ≤ Ω)
    (hsp : ∀ α : 𝓞 E, (α : E) ∈ Submodule.span ℚ (Set.range fun j => (ω j : E)))
    {I : Submodule ℤ (Vsp X.dim)} (hI : Good X (1 / (Ω * th)) I) {x : Vsp X.dim} (hx : x ∈ X.L)
    (hxI : x ∉ I) (hd : Metric.infDist x (IR I) < th) :
    ∃ J, Good X (1 / (Ω * th)) J ∧ Module.finrank ℝ (IR I) < Module.finrank ℝ (IR J) := by sorry
