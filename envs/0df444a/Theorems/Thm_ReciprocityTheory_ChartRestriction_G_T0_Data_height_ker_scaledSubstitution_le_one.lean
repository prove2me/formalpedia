-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_height_ker_scaledSubstitution_le_one
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.height_ker_scaledSubstitution_le_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:35:55.768092+00:00
-- url     : https://prove2.me/theorems/3cfe8106-60c0-572a-b40d-27dd3bc70940
-- title:
--   Data: height ker scaled Substitution le one
-- statement:
--   The Data construction uses the height ker scaled Substitution le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HeightKerScaledSubstitutionLeOne.lean#L19-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HeightKerScaledSubstitutionLeOne.lean#L19-L84

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AevalElimEqRenameLinearSubstitution
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraicIndependentScaledForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HeightKerScaledSubstitutionLeOne
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

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.height_ker_scaledSubstitution_le_one (hd : d.AxH 𝒜) (c : ι) : (RingHom.ker (d.scaledSubstitution c)).height ≤ 1 := by sorry
