-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_nLa_supp
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.nLa_supp
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T17:23:30.454261+00:00
-- url     : https://prove2.me/theorems/04240335-fddf-4aac-a33d-21857445625c
-- title:
--   Data: n La supp
-- statement:
--   The Data construction uses the n La supp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HHINDC.lean#L214-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HHINDC.lean#L214-L229

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UniformizerOfResidueIndep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed MeasureTheory IsDedekindDomain
  ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.nLa_supp (hd : d.AxH 𝒜) (h : d.S1) (O : ∀ c, AddValuation (Ω c) (WithTop ℤ) → A c → ℤ)
    (c : ι) (f : A c) (a : Ω c) (ha : a ≠ 0)
    (hOs : ∀ v, d.admitted c v → ((O c v (a • f) : ℤ) : WithTop ℤ) = v a + (O c v f : WithTop ℤ)) :
    Function.support (fun la => d.nLa h c la (algebraMap (Ω c) (OmS (Ω c) d.D d.N) a)) ⊆
      {la : HeightOneSpectrum (𝓞 K) | ∃ w ∈ d.PlOver la c, O c (d.Wres c w) f ≠ 0} ∪
      {la : HeightOneSpectrum (𝓞 K) | ∃ w ∈ d.PlOver la c, O c (d.Wres c w) (a • f) ≠ 0} := by sorry
