-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_nsg_smul
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.nsg_smul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T17:07:18.615583+00:00
-- url     : https://prove2.me/theorems/f8f05f40-018d-52d3-ab8c-93f4ea0c54a5
-- title:
--   Data: nsg smul
-- statement:
--   The Data construction uses the nsg smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HHINDC.lean#L176-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HHINDC.lean#L176-L199

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

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.nsg_smul (hd : d.AxH 𝒜) (h : d.S1) (Nr : ∀ c, A c → (Ω c →+* ℂ) → ℝ) (c : ι) (f : A c)
    (a : Ω c) (ha : a ≠ 0) (hNs : ∀ P, Nr c (a • f) P = ‖P a‖ * Nr c f P) (hN0 : ∀ P, Nr c f P ≠ 0)
    (sg : K →+* ℂ) (hI : Integrable (d.aI Nr c f sg) (blockSphereProb d.D (d.N + 1)))
    (hI' : Integrable (d.aI Nr c (a • f) sg) (blockSphereProb d.D (d.N + 1))) :
    ∫ z, (∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)), -Real.log (Nr c (a • f) P))
        ∂(blockSphereProb d.D (d.N + 1)) =
      ∫ z, (∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)), -Real.log (Nr c f P))
        ∂(blockSphereProb d.D (d.N + 1)) - ∫ z, d.lsum c sg a z ∂(blockSphereProb d.D (d.N + 1)) := by sorry
