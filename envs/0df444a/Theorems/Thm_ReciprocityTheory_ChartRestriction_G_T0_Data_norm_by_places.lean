-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_norm_by_places
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.norm_by_places
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:58:35.284918+00:00
-- url     : https://prove2.me/theorems/b86538d5-9d2e-44e6-8581-1017530cc0c2
-- title:
--   Data: norm by places
-- statement:
--   The Data construction uses the norm by places property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/NormByPlaces.lean#L220-L330
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/NormByPlaces.lean#L220-L330

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormByPlaces
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

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.norm_by_places (hd : d.AxH 𝒜) (h : d.S1) (c : ι) :
    (∀ p ∈ d.HtOne, (d.OverP c p).Finite) ∧
    ∀ y : OmS (Ω c) d.D d.N, y ≠ 0 →
      {p | p ∈ d.HtOne ∧ ∃ w ∈ d.OverP c p, w y ≠ 0}.Finite ∧
      ∃ κ : K, κ ≠ 0 ∧
        letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
        Algebra.norm (KTf K d.D d.N) y =
          algebraMap K (KTf K d.D d.N) κ *
            ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
              algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^
                (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.OverP c p),
                  (d.fze h c w : ℤ) * WithTop.untopD 0 (w y)) := by sorry
