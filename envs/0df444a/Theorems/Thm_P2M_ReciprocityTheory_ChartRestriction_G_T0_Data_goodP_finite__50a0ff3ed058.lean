-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_T0_Data_goodP_finite__50a0ff3ed058
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_T0_Data_goodP_finite__50a0ff3ed058
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T17:15:53.188805+00:00
-- url     : https://prove2.me/theorems/2771dd99-a7a8-50db-8b75-81331d187d59
-- title:
--   P2 M Reciprocity Theory Chart Restriction G T0 Data good P finite  50a0ff3ed058: P2 M Reciprocity Theory Chart Restriction G T0 Data good P finite  50a0ff3ed058
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G T0 Data good P finite  50a0ff3ed058 construction uses the P2 M Reciprocity Theory Chart Restriction G T0 Data good P finite  50a0ff3ed058 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HHINDC.lean#L110-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HHINDC.lean#L110-L112

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_T0_Data_goodP_finite__50a0ff3ed058 (hd : d.AxH 𝒜) (h : d.S1) (c : ι) {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) :
    (d.GoodP c p).Finite := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«T0».«Data».«goodP_finite'» := P2M_ReciprocityTheory_ChartRestriction_G_T0_Data_goodP_finite__50a0ff3ed058
