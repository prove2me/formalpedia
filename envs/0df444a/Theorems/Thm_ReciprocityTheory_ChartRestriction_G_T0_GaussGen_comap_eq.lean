-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_comap_eq
-- name    : ReciprocityTheory.ChartRestriction.G.T0.GaussGen.comap_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:37:36.885082+00:00
-- url     : https://prove2.me/theorems/a4dc7c9c-dd2f-476c-9970-4fc37a479dfa
-- title:
--   Gauss Gen: comap eq
-- statement:
--   The Gauss Gen construction uses the comap eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussGenericHeight/GaussGenericStatements/GaussGenericLemmas/TranslationDomainMaps/TranslSEquivApply.lean#L149-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussGenericHeight/GaussGenericStatements/GaussGenericLemmas/TranslationDomainMaps/TranslSEquivApply.lean#L149-L209

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtLeafSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussGenericHeight_GaussGenericStatements_GaussGenericLemmas_TranslationDomainMaps_MapDomainMemOfDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussGenericHeight_GaussGenericStatements_GaussGenericLemmas_TranslationDomainMaps_TranslSEquivApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.GaussGen
open MvPolynomial NumberField BlockPoly
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)) (d : Data K ι Ω WT A)

theorem ReciprocityTheory.ChartRestriction.G.T0.GaussGen.comap_eq (hx1 : LeafSt.PlaceTrivialOrPositive 𝒜 d) (hx2 : LeafSt.AdmissibleValuationPrimeUnique 𝒜 d)
    (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (p : Ideal (KTp K d.D d.N)) (hp : p ∈ d.HtOne)
    (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (hw : w ∈ d.GoodP c p)
    (σ : KTp K d.D d.N ≃ₐ[K] KTp K d.D d.N)
    (τ : MvPolynomial (SVar d.D d.N) (Ω c) ≃ₐ[Ω c] MvPolynomial (SVar d.D d.N) (Ω c))
    (hc : ∀ t, τ (Pimg (d.jc c) (d.x c) t) = aeval (Pimg (d.jc c) (d.x c)) (σ (X t))) :
    p.comap σ = p := by sorry
