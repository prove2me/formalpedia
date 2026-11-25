-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_ker_eval_eq_of_place
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.ker_eval_eq_of_place
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:12:37.211782+00:00
-- url     : https://prove2.me/theorems/4152ee61-8a20-5bae-bcbf-f08528e1ae27
-- title:
--   Data: ker eval eq of place
-- statement:
--   The Data construction uses the ker eval eq of place property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/KerPLeOfPlace.lean#L237-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/KerPLeOfPlace.lean#L237-L257

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GeneratorNeZeroOfHeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ScaleMultiHomogeneous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KerPLeOfPlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.ker_eval_eq_of_place (hd : d.AxH 𝒜) (c : ι) {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne)
    {w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)} (hw : w ∈ d.OverP c p)
    (htriv : ∀ a : Ω c, a ≠ 0 → d.Wres c w a = 0) (hy : 0 < w (d.rationalBaseRow c)) :
    kerP (K := K) (D := d.D) (d.jc c) (d.x c) = p := by sorry
