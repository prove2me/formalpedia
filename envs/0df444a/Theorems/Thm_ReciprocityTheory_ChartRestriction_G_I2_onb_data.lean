-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_onb_data
-- name    : ReciprocityTheory.ChartRestriction.G.I2.onb_data
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:29:52.894589+00:00
-- url     : https://prove2.me/theorems/fb4c5e24-c3b8-4928-b2b6-559047a6692a
-- title:
--   I2: onb data
-- statement:
--   The I2 construction uses the onb data property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/HfEqInner.lean#L110-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/HfEqInner.lean#L110-L196

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_HfEqInner
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
noncomputable section
variable {E : Type} [Field E] [NumberField E]

theorem ReciprocityTheory.ChartRestriction.G.I2.onb_data (X : PT E) (I : Submodule ℤ (Vsp X.dim)) (σ : E →+* ℂ) (ρ : ℕ)
    (hρ : Module.finrank ℂ (Submodule.span ℂ (I : Set (Vsp X.dim)) ⊓ VP σ : Submodule ℂ _) = ρ)
    (hst : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I)
    (w : Fin ρ → Vsp X.dim) (hw : ∀ s, InPart σ (w s) ∧ w s ∈ Submodule.span ℂ (I : Set (Vsp X.dim)))
    (hon : ∀ s s', Hf (w s) (w s') = if s = s' then 1 else 0) :
    ∃ (N : ℕ) (b : Fin N → Vsp X.dim), N ≤ X.r ∧ ρ ≤ N ∧
      (∀ k (h : k.val < ρ), b k = w ⟨k, h⟩) ∧
      (∀ k, InPart σ (b k)) ∧
      (∀ k, ρ ≤ k.val → ‖b k‖ = 1 ∧ ∀ a ∈ I, Hf (b k) a = 0) ∧
      (∀ x y : Vsp X.dim, InPart σ x → InPart σ y → ∑ k, Hf x (b k) * Hf (b k) y = Hf x y) := by sorry
