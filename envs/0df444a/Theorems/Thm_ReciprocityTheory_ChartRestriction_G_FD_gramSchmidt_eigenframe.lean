-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_gramSchmidt_eigenframe
-- name    : ReciprocityTheory.ChartRestriction.G.FD.gramSchmidt_eigenframe
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:22:33.937743+00:00
-- url     : https://prove2.me/theorems/f0445b80-224c-455d-83f9-9b77836ba0c8
-- title:
--   FD: gram Schmidt eigenframe
-- statement:
--   The FD construction uses the gram Schmidt eigenframe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/GramSchmidtEigenframe.lean#L58-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/GramSchmidtEigenframe.lean#L58-L148

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExistsUnitaryBasisSameFlag
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MmatUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramSchmidtEigenframe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Matrix
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem ReciprocityTheory.ChartRestriction.G.FD.gramSchmidt_eigenframe (r : ℕ) (X : DataX E r) (ξ : Fin r → E) (z0 : Frame X.Ψ r)
    (f Y : X.Ψ → Fin (r - 2) → Fin r → ℂ) (hξ : X.IsIso ξ) (hz : z0 ∈ X.dom) (hf : X.UBasis z0 ξ f)
    (hYind : ∀ τ, LinearIndependent ℂ (Y τ))
    (hYU : ∀ τ j, Y τ j ∈ Submodule.span ℂ (Set.range (f τ)))
    (hYorth : ∀ τ (j k : Fin (r - 2)), (j : ℕ) < X.p0 - 1 → X.p0 - 1 ≤ (k : ℕ) →
      hermC τ.1 X.Gm (Y τ j) (Y τ k) = 0)
    (hYpos : ∀ τ (w : Fin (r - 2) → ℂ), (∀ j : Fin (r - 2), X.p0 - 1 ≤ (j : ℕ) → w j = 0) → w ≠ 0 →
      0 < (hermC τ.1 X.Gm (∑ j, w j • Y τ j) (∑ j, w j • Y τ j)).re)
    (hYneg : ∀ τ (w : Fin (r - 2) → ℂ), (∀ j : Fin (r - 2), (j : ℕ) < X.p0 - 1 → w j = 0) → w ≠ 0 →
      (hermC τ.1 X.Gm (∑ j, w j • Y τ j) (∑ j, w j • Y τ j)).re < 0) :
    ∃ h1 : X.Ψ → Matrix (Fin r) (Fin r) ℂ, X.IsUnitaryC h1 ∧
      (∀ s t : X.Ψ → ℂ, X.applyV h1 (X.lineV ξ s + X.Jz z0 (X.lineV ξ t)) =
        X.lineV ξ s + X.Jz z0 (X.lineV ξ t)) ∧
      (∀ u ∈ X.Uz z0 ξ, X.applyV h1 u ∈ X.Uz z0 ξ) ∧
      (∀ τ (v : Fin r → ℂ), v ∈ Submodule.span ℂ (f τ '' {k | (k : ℕ) < X.p0 - 1}) →
        (h1 τ) *ᵥ v ∈ Submodule.span ℂ (Y τ '' {j | (j : ℕ) < X.p0 - 1})) ∧
      (∀ τ (j : Fin (r - 2)), ∃ u : Fin r → ℂ,
        u ∈ Submodule.span ℂ (f τ '' {k | ((k : ℕ) < X.p0 - 1 ↔ (j : ℕ) < X.p0 - 1)}) ∧ (h1 τ) *ᵥ u = Y τ j) := by sorry
