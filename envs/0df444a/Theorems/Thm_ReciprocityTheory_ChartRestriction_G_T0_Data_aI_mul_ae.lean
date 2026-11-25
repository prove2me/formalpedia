-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_aI_mul_ae
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.aI_mul_ae
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T17:31:09.082495+00:00
-- url     : https://prove2.me/theorems/3d0b8e06-d2aa-5c07-b556-e30f3b43e90c
-- title:
--   Data: a I mul ae
-- statement:
--   The Data construction uses the a I mul ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HHINDD.lean#L125-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HHINDD.lean#L125-L136

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

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.aI_mul_ae (hd : d.AxH 𝒜) (h : d.S1) {G G' : WT} (c : ι) {f g : A c}
    (hf : f ∈ 𝒜 c G) (hg : g ∈ 𝒜 c G') (hf0 : f ≠ 0) (hg0 : g ≠ 0) (sg : K →+* ℂ) :
    d.aI (fun c f P => d.nrm c (G + G') f P) c (f * g) sg =ᵐ[blockSphereProb d.D (d.N + 1)]
      fun z => d.aI (fun c f P => d.nrm c G f P) c f sg z + d.aI (fun c f P => d.nrm c G' f P) c g sg z := by sorry
