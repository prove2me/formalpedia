-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_IntegralRingEmbedding_span_of_eigen
-- name    : ReciprocityTheory.ChartRestriction.G.H1.IntegralRingEmbedding.span_of_eigen
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:25:18.381564+00:00
-- url     : https://prove2.me/theorems/95df0dd9-2c39-42a6-b93f-d7c0c2358c5e
-- title:
--   Integral Ring Embedding: span of eigen
-- statement:
--   The Integral Ring Embedding construction uses the span of eigen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/IntegralRingEmbedding.lean#L150-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/IntegralRingEmbedding.lean#L150-L274

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_NakayamaChar
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_IntegralRingEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.IntegralRingEmbedding
open Module
variable {F : Type} [Field F] (v : AddValuation F (WithTop ℚ))
variable {W : Type} [AddCommGroup W] [Module F W] {n : ℕ} (b : Fin n → W)

theorem ReciprocityTheory.ChartRestriction.G.H1.IntegralRingEmbedding.span_of_eigen (UU Pos : W → Prop) (hb : LinearIndependent F b)
    (hUU : ∀ s, UU s ↔ ∃ c : Fin n → F, (∀ i, 0 ≤ v (c i)) ∧ s = ∑ i, c i • b i)
    (hPos : ∀ s, UU s → ∀ ζ : F, ∀ s', 0 < v ζ → UU s' → s = ζ • s' → Pos s)
    (hπ : ∃ π : F, 0 < v π)
    {ι Γ : Type} [Fintype ι] (hcard : Fintype.card ι = n) (sv : ι → W)
    (hsv : ∀ i, UU (sv i)) (hsvp : ∀ i, ¬ Pos (sv i))
    (T : Γ → W →ₗ[F] W) (hT : ∀ γ s, UU s → UU (T γ s))
    {N : ℕ} (hN : 1 ≤ N) (hvN : v (N : F) = 0) (χ : ι → Γ → F)
    (hχN : ∀ i γ, χ i γ ^ N = 1) (heig : ∀ i γ, T γ (sv i) = χ i γ • sv i)
    (hsep : ∀ i j, i ≠ j → ∃ γ, χ i γ ≠ χ j γ) :
    ∀ s, UU s → ∃ a : ι → F, (∀ i, 0 ≤ v (a i)) ∧ s = ∑ i, a i • sv i := by sorry
