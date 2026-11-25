-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_disc_product
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.disc_product
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T17:35:08.342153+00:00
-- url     : https://prove2.me/theorems/682dd846-ec96-52ed-91b9-4a9b44875b07
-- title:
--   Data: disc product
-- statement:
--   The Data construction uses the disc product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/DiscProduct.lean#L21-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/DiscProduct.lean#L21-L131

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscBDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteHeightFractionRepr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_DiscProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.disc_product (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) (a b : KTp K d.D d.N)
    (hab : d.IsPres hd h a b) (Om : KTp K d.D d.N)
    (hOm : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Om = d.omE hd h) :
    (Function.support fun la => d.gOrd la (d.De hd h)).Finite ∧
    (Function.support fun la => d.NlaG h d.wF hd.a4.choose la).Finite ∧
    (∑ᶠ la, ((d.gOrd la (d.De hd h) : ℝ) + 2 * d.NlaG h d.wF hd.a4.choose la) * logNorm la) /
        (Module.finrank ℚ K : ℝ) =
      meanK (fun sg => d.mSgP sg a b - 2 * d.Nsg d.wF hd.a4.choose sg) -
        ReciprocityTheory.MultiplicativeHeights.h0 Om + 2 * d.Hgt h d.wF hd.a4.choose := by sorry
