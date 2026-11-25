-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_arithDegree_additive
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.arithDegree_additive
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:38:18.409107+00:00
-- url     : https://prove2.me/theorems/377cb979-aac5-4af1-b816-8fc54caeffce
-- title:
--   Data: arith Degree additive
-- statement:
--   The Data construction uses the arith Degree additive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/NormFactorizationClause.lean#L288-L340
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/NormFactorizationClause.lean#L288-L340

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

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.arithDegree_additive (hd : d.AxH 𝒜) (h : d.S1) :
    (∀ (G : WT) (ta ta' : ∀ c, A c), (∀ c, ta c ∈ 𝒜 c G ∧ ta c ≠ 0) →
      (∀ c, ta' c ∈ 𝒜 c G ∧ ta' c ≠ 0) → d.aG h G ta = d.aG h G ta') ∧
    (∀ (G G' : WT) (ta ta' : ∀ c, A c), (∀ c, ta c ∈ 𝒜 c G ∧ ta c ≠ 0) →
      (∀ c, ta' c ∈ 𝒜 c G' ∧ ta' c ≠ 0) → d.aG h (G + G') (ta * ta') = d.aG h G ta + d.aG h G' ta') := by sorry
