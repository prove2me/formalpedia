-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_T0_Data_Hgt_pow__5806f9ec6fcd
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_T0_Data_Hgt_pow__5806f9ec6fcd
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-27T05:48:09.997401+00:00
-- url     : https://prove2.me/theorems/6ed1588b-cc2f-4ab0-ab1f-40995c002a1c
-- title:
--   P2 M Reciprocity Theory Chart Restriction G T0 Data Hgt pow  5806f9ec6fcd: P2 M Reciprocity Theory Chart Restriction G T0 Data Hgt pow  5806f9ec6fcd
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G T0 Data Hgt pow  5806f9ec6fcd construction uses the P2 M Reciprocity Theory Chart Restriction G T0 Data Hgt pow  5806f9ec6fcd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HHINDE.lean#L73-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HHINDE.lean#L73-L78

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IntNsg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LogHeightGeneratorLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IntegralLeOfAeLeAffine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LogNormNonneg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDE
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

theorem P2M_ReciprocityTheory_ChartRestriction_G_T0_Data_Hgt_pow__5806f9ec6fcd (hd : d.AxH 𝒜) (h : d.S1) (G : WT) (f : ∀ c, A c)
    (hf : ∀ c, f c ∈ 𝒜 c G ∧ f c ≠ 0) (hI : d.IntOK G f) (n : ℕ) (hn : 0 < n) :
    (∀ c, (f ^ n) c ∈ 𝒜 c (n • G) ∧ (f ^ n) c ≠ 0) ∧ d.IntOK (n • G) (f ^ n) ∧
      d.Hgt h (n • G) (f ^ n) = (n : ℝ) * d.Hgt h G f := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«T0».«Data».«Hgt_pow'» := P2M_ReciprocityTheory_ChartRestriction_G_T0_Data_Hgt_pow__5806f9ec6fcd
