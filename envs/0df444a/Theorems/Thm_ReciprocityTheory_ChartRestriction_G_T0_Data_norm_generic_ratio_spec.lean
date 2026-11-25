-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_norm_generic_ratio_spec
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.norm_generic_ratio_spec
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:40:39.796954+00:00
-- url     : https://prove2.me/theorems/bbc29bf0-b814-4b3a-bff2-f04bda5e2774
-- title:
--   Data: norm generic ratio spec
-- statement:
--   The Data construction uses the norm generic ratio spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/NormGenericRatioSpec.lean#L51-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/NormGenericRatioSpec.lean#L51-L122

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BasisBlock0
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormGenericRatioSpec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.norm_generic_ratio_spec (hd : d.AxH 𝒜) (h : d.S1) (c : ι) :
    ∃ P Q : KTp K d.D d.N, Q ≠ 0 ∧ (∀ x, d.sub0 x Q = Q) ∧
      (letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra;
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) P =
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Q * Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c)) ∧
      ∀ x : Fin (d.N + 1) → K, d.wx x c ≠ 0 →
        (letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra;
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.sub0 x P) =
            algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Q *
              Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N)
                (ratio (Ω := Ω c) (d.wx x c) (d.w (d.jc c) c)))) := by sorry
