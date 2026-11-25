-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_norm_at_la
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.norm_at_la
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:10:32.758059+00:00
-- url     : https://prove2.me/theorems/447596ea-f4ad-4d1c-bbbe-7d9a8a8cf656
-- title:
--   Data: norm at la
-- statement:
--   The Data construction uses the norm at la property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HNormPts.lean#L21-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HNormPts.lean#L21-L30

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormPtsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormPtsB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormPts
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

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.norm_at_la (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (ϖ : 𝓞 K) (hϖ : ϖ ∈ la.asIdeal) (hϖ2 : ϖ ∉ la.asIdeal ^ 2)
    (y : OmS (Ω c) d.D d.N) (hy : y ≠ 0) :
    ∃ u : Op d.D d.N la, IsUnit u ∧
      letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
      Algebra.norm (KTf K d.D d.N) y =
        (algebraMap K (KTf K d.D d.N) (ϖ : K)) ^
          (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.PlOver la c),
            (d.fze h c w : ℤ) * WithTop.untopD 0 (w y)) * OpToKT d.D d.N la u := by sorry
