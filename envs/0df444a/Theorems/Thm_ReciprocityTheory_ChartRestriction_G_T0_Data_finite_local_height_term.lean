-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_finite_local_height_term
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.finite_local_height_term
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-27T06:03:20.4774+00:00
-- url     : https://prove2.me/theorems/c03b416b-79c8-4a6b-911c-d8ca8eabe953
-- title:
--   Data: finite local height term
-- statement:
--   The Data construction uses the finite local height term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FiniteLocalHeightTerm.lean#L19-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FiniteLocalHeightTerm.lean#L19-L151

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ArchimedeanLocalHeightTerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteLocalHeightTerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MeasureTheory ReciprocityTheory.MultiplicativeHeights
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.finite_local_height_term (hd : d.AxH 𝒜) (h : d.S1) (x : Fin (d.N + 1) → K)
    (hx : ∀ c, d.wx x c ≠ 0) (c : ι) (F : KTp K d.D d.N) (κ : K) (hκ : κ ≠ 0)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c)
    (hFne : F ≠ 0) (hFx : d.translatedForm x F ≠ 0) (hs : d.heightSubstitutionCondition h x c F κ)
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    d.localHeightAtPrime h (d.wx x) c la * logNorm la =
      Real.log (gaussAbs (FinitePlace.mk la) F) -
        Real.log (gaussAbs (FinitePlace.mk la) (d.translatedForm x F)) +
        Real.log (FinitePlace.mk la κ) := by sorry
