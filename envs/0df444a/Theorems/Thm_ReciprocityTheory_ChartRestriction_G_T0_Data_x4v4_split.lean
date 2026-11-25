-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_x4v4_split
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.x4v4_split
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:53:45.293389+00:00
-- url     : https://prove2.me/theorems/776c307c-1489-431a-87e5-b8b7863d66ff
-- title:
--   Data: x4v4 split
-- statement:
--   The Data construction uses the x4v4 split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/X4v4RatioSpec.lean#L95-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/X4v4RatioSpec.lean#L95-L106

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BasisBlock0
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormFactorizationClause
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_X4v4RatioSpec
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

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.x4v4_split (hd : d.AxH 𝒜) (h : d.S1) (c : ι) {p : Ideal (KTp K d.D d.N)}
    (hp : p ∈ d.HtOne) {f : A c} (hf : f ∈ 𝒜 c d.wL) (hf0 : f ≠ 0) :
    d.nPMM h c f p =
      (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
        (d.fze h c w : ℤ) * WithTop.untopD 0 (d.Wres c w (ratio (Ω := Ω c) f (d.w (d.jc c) c)))) +
      d.nPMM h c (d.w (d.jc c) c) p := by sorry
