-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_T0_Data_exists_ne_zero_of_finsum_mem_ne_zero__a210564d8b11
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_T0_Data_exists_ne_zero_of_finsum_mem_ne_zero__a210564d8b11
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-27T05:44:59.045414+00:00
-- url     : https://prove2.me/theorems/52856f8c-826c-4fbe-b12e-e1b7f41a1700
-- title:
--   P2 M Reciprocity Theory Chart Restriction G T0 Data exists ne zero of finsum mem ne zero  a210564d8b11: P2 M Reciprocity Theory Chart Restriction G T0 Data exists ne zero of finsum mem ne zero  a21056
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G T0 Data exists ne zero of finsum mem ne zero  a210564d8b11 construction uses the P2 M Reciprocity Theory Chart Restriction G T0 Data exists ne zero of finsum mem ne zero  a210564d8b11 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ValuationGenericRatioEqRestriction.lean#L87-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ValuationGenericRatioEqRestriction.lean#L87-L91

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UniformizerOfResidueIndep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormFactorizationClause
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ComponentFormProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IntNsg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormByPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormPts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HPlaces
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OrdEqValuationRatioBaseAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SpecialFibreFactorization
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationGenericRatioEqRestriction
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_SpecialFibreFactorization

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_T0_Data_exists_ne_zero_of_finsum_mem_ne_zero__a210564d8b11 {α M : Type*} [AddCommMonoid M] {s : Set α} {f : α → M}
    (h : ∑ᶠ i ∈ s, f i ≠ 0) : ∃ i ∈ s, f i ≠ 0 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«T0».«Data».«exists_ne_zero_of_finsum_mem_ne_zero'» := P2M_ReciprocityTheory_ChartRestriction_G_T0_Data_exists_ne_zero_of_finsum_mem_ne_zero__a210564d8b11
