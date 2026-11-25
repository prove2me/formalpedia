-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_LocalLengthFraction_local_len
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalLengthFraction.local_len
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:22:19.402944+00:00
-- url     : https://prove2.me/theorems/b7bc23a6-3a00-4227-b9f1-b08984a3177b
-- title:
--   Local Length Fraction: local len
-- statement:
--   The Local Length Fraction construction uses the local len property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/LocalLengthFraction.lean#L16-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/LocalLengthFraction.lean#L16-L132

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QuotShiftPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FreeQuotPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_LocalLengthFraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalLengthFraction
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FreeQuotientRank ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.QuotShiftPfH
variable {K₁ : Type} [Field K₁] [NumberField K₁] (w : HeightOneSpectrum (𝓞 K₁))
variable {U : Type} [AddCommGroup U] [Module K₁ U] [FiniteDimensional K₁ U]
  [Module (Rv K₁ w) U] [IsScalarTower (Rv K₁ w) K₁ U]

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalLengthFraction.local_len (hL : QuotLocalStatement) (P : Submodule K₁ U) (Mw : Submodule (Rv K₁ w) U)
    (hMw : Mw.FG) (hMspan : Submodule.span K₁ (Mw : Set U) = ⊤) {ρ : ℕ}
    (hρ : finrank K₁ (U ⧸ P) = ρ) (e : Fin ρ → U) (he : ∀ j, e j ∈ Mw)
    (c : Fin ρ → U →ₗ[K₁] K₁) (hcP : ∀ i, ∀ x ∈ P, c i x = 0) (s : Fin ρ → ℝ) (β : ℝ)
    (hint : ∀ i, ∀ y ∈ Mw, c i y ≠ 0 → -β ≤ (ordAt w (c i y) : ℝ) + s i)
    (hdet : (Matrix.of fun i j => c i (e j)).det ≠ 0) :
    ∃ n : ℕ, Module.length (Rv K₁ w) (Mw ⧸ ((Submodule.span (Rv K₁ w) (P : Set U) ⊓ Mw) ⊔
        Submodule.span (Rv K₁ w) (Set.range e)).comap Mw.subtype) = n ∧
      (n : ℝ) ≤ (ordAt w (Matrix.of fun i j => c i (e j)).det : ℝ) + ∑ i, s i + ρ * β := by sorry
