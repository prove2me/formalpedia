-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_rank_iso
-- name    : ReciprocityTheory.ChartRestriction.G.I2.rank_iso
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:52:11.079122+00:00
-- url     : https://prove2.me/theorems/4e5932f2-e8ee-4b6b-b1c0-c8b1658eebe6
-- title:
--   I2: rank iso
-- statement:
--   The I2 construction uses the rank iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitR.lean#L120-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitR.lean#L120-L272

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitR
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

theorem ReciprocityTheory.ChartRestriction.G.I2.rank_iso [IsCMField E] (X : PT E) (I : Submodule ℤ (Vsp X.dim)) (hle : I ≤ X.L)
    (hst : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I) (hiso : ∀ x ∈ I, ∀ y ∈ I, (Hf x y).im = 0) :
    ∃ ρ, (∀ τ, ρ ≤ X.dim τ) ∧ Module.finrank ℝ (IR I) = 2 * PT.f E * ρ := by sorry
