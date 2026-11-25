-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_finite_height_fraction_repr
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.finite_height_fraction_repr
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T16:09:32.926572+00:00
-- url     : https://prove2.me/theorems/9eb0c8ec-9397-493b-84b1-b4e94976ec32
-- title:
--   Data: finite height fraction repr
-- statement:
--   The Data construction uses the finite height fraction repr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FiniteHeightFractionRepr.lean#L31-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FiniteHeightFractionRepr.lean#L31-L125

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SphereMeanSubArchimedean
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteHeightFractionRepr
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

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.finite_height_fraction_repr (hd : d.AxH 𝒜) (h : d.S1) :
    ∃ U V : KTp K d.D d.N, U ≠ 0 ∧ V ≠ 0 ∧ (∃ eU, IsMultiHomogeneous eU U) ∧
      (∃ eV, IsMultiHomogeneous eV V) ∧
      d.fDivE hd h * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) V =
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) U ∧
      d.h0f h d.wF hd.a4.choose = h0 U - h0 V := by sorry
