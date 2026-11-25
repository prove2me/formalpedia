-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_emb_ext
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.emb_ext
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:36:04.831922+00:00
-- url     : https://prove2.me/theorems/6fa96afc-05ec-5acf-a253-78b9ec7c568e
-- title:
--   Data: emb ext
-- statement:
--   The Data construction uses the emb ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SacSuccAbove.lean#L160-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SacSuccAbove.lean#L160-L178

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SacSuccAbove
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
variable (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (sg : K →+* ℂ) (pt : TVar d.D d.N → ℂ)
  (hpt : ∀ q : MvPolynomial (TVar d.D d.N) K, q ≠ 0 → eval₂ sg pt q ≠ 0)

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.emb_ext (σ₁ σ₂ : OmS (Ω c) d.D d.N →+* ℂ) (h₁ : σ₁.comp (d.KTtoS h c) = tauPev sg pt hpt)
    (h₂ : σ₂.comp (d.KTtoS h c) = tauPev sg pt hpt)
    (he : σ₁.comp (algebraMap (Ω c) _) = σ₂.comp (algebraMap (Ω c) _)) : σ₁ = σ₂ := by sorry
