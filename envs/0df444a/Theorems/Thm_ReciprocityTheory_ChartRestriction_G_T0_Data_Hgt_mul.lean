-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_Hgt_mul
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.Hgt_mul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T17:37:04.156862+00:00
-- url     : https://prove2.me/theorems/df90f329-1319-4638-a637-e984b0ebb7c8
-- title:
--   Data: Hgt mul
-- statement:
--   The Data construction uses the Hgt mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HHINDD.lean#L138-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HHINDD.lean#L138-L226

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDD
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

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.Hgt_mul (hd : d.AxH 𝒜) (h : d.S1) (G G' : WT) (f g : ∀ c, A c)
    (hf : ∀ c, f c ∈ 𝒜 c G ∧ f c ≠ 0) (hg : ∀ c, g c ∈ 𝒜 c G' ∧ g c ≠ 0)
    (hIf : d.IntOK G f) (hIg : d.IntOK G' g) :
    d.IntOK (G + G') (f * g) ∧ d.Hgt h (G + G') (f * g) = d.Hgt h G f + d.Hgt h G' g := by sorry
