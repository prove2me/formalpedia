-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_T0_Data_use__fb60b9f90987
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_T0_Data_use__fb60b9f90987
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:38:32.117327+00:00
-- url     : https://prove2.me/theorems/f59efb2b-77c9-4728-9ded-0b12b2fe7959
-- title:
--   P2 M Reciprocity Theory Chart Restriction G T0 Data use  fb60b9f90987: P2 M Reciprocity Theory Chart Restriction G T0 Data use  fb60b9f90987
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G T0 Data use  fb60b9f90987 construction uses the P2 M Reciprocity Theory Chart Restriction G T0 Data use  fb60b9f90987 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/NormFactorizationClause.lean#L268-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/NormFactorizationClause.lean#L268-L286

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_T0_Data_use__fb60b9f90987 (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (r : Ω c) (hr : r ≠ 0) :
    {p | p ∈ d.HtOne ∧ (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ))
      (_ : w ∈ d.GoodP c p), (d.fze h c w : ℤ) * WithTop.untopD 0 (d.Wres c w r)) ≠ 0}.Finite := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«T0».«Data».«use₈» := P2M_ReciprocityTheory_ChartRestriction_G_T0_Data_use__fb60b9f90987
