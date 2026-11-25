-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_finsum_liesOver_eq_finsum_good
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.finsum_liesOver_eq_finsum_good
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:37:36.198801+00:00
-- url     : https://prove2.me/theorems/df277f87-08dc-5283-95e9-0ef5a2fc5174
-- title:
--   Data: finsum lies Over eq finsum good
-- statement:
--   The Data construction uses the finsum lies Over eq finsum good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/NormFactorizationClause.lean#L23-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/NormFactorizationClause.lean#L23-L43

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormByPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UniformizerOfResidueIndep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ScaleMultiHomogeneous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormFactorizationClause
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

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.finsum_liesOver_eq_finsum_good (c : ι) (p : Ideal (KTp K d.D d.N)) (g : Ω c) (hg : g ≠ 0)
    (F : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ) → WithTop ℤ → ℤ)
    (hF : ∀ w, F w 0 = 0) :
    (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.OverP c p),
      F w (w (algebraMap (Ω c) (OmS (Ω c) d.D d.N) g))) =
    ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
      F w (d.Wres c w g) := by sorry
