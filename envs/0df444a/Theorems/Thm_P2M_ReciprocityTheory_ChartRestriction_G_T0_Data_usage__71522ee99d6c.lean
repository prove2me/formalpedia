-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_T0_Data_usage__71522ee99d6c
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_T0_Data_usage__71522ee99d6c
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T17:10:38.774854+00:00
-- url     : https://prove2.me/theorems/12a8574a-ffb5-4a70-80aa-bfeda23fb5a2
-- title:
--   P2 M Reciprocity Theory Chart Restriction G T0 Data usage  71522ee99d6c: P2 M Reciprocity Theory Chart Restriction G T0 Data usage  71522ee99d6c
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G T0 Data usage  71522ee99d6c construction uses the P2 M Reciprocity Theory Chart Restriction G T0 Data usage  71522ee99d6c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HHINDC.lean#L114-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HHINDC.lean#L114-L124

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_T0_Data_usage__71522ee99d6c (hd : d.AxH 𝒜) (h : d.S1) (O : ∀ c, AddValuation (Ω c) (WithTop ℤ) → A c → ℤ)
    (c : ι) (f : A c) (a : Ω c) (ha : a ≠ 0)
    (hOs : ∀ v, d.admitted c v → ((O c v (a • f) : ℤ) : WithTop ℤ) = v a + (O c v f : WithTop ℤ))
    {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) :
    d.anP h O c (a • f) p = d.anP h O c f p + d.nPa h c p a := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«T0».«Data».«usage₆» := P2M_ReciprocityTheory_ChartRestriction_G_T0_Data_usage__71522ee99d6c
