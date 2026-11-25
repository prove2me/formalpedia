-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_norm_at_sg_B
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.norm_at_sg_B
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:36:22.429144+00:00
-- url     : https://prove2.me/theorems/66d4747e-b9c7-5bb4-9aca-6d4287854260
-- title:
--   Data: norm at sg B
-- statement:
--   The Data construction uses the norm at sg B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HNormPtsB.lean#L90-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HNormPtsB.lean#L90-L148

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CastAddNeNatAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SacSuccAbove
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormPtsB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial MeasureTheory
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.norm_at_sg_B (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (sg : K →+* ℂ) :
    letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
    ∀ᵐ z ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)),
      (d.ST c sg (d.tOf z)).Finite ∧ (d.ST c sg (d.tOf z)).ncard = d.delc c ∧
      (∀ (g : Ω c) (a b : KTp K d.D d.N) (t0 : Fin (d.N + 1) → ℂ), g ≠ 0 → b ≠ 0 →
        (Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N) g) *
            algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b =
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a) →
        d.evT sg t0 (d.tOf z) b ≠ 0 → d.evT sg t0 (d.tOf z) a / d.evT sg t0 (d.tOf z) b = ∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)), P g) ∧
      (∀ (a b : KTp K d.D d.N) (t0 : Fin (d.N + 1) → ℂ), b ≠ 0 →
        (Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c) * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b =
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a) →
        d.evT sg t0 (d.tOf z) b ≠ 0 → d.evT sg t0 (d.tOf z) a / d.evT sg t0 (d.tOf z) b = ∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)),
          ∑ j, t0 j * P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))) := by sorry
