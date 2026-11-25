-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_eq_ratio_smul_on_line
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.eq_ratio_smul_on_line
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:04:36.499415+00:00
-- url     : https://prove2.me/theorems/20b3e542-56c1-48f6-a52b-17046d8234c5
-- title:
--   Data: eq ratio smul on line
-- statement:
--   The Data construction uses the eq ratio smul on line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GeneratorNeZeroOfHeight.lean#L37-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GeneratorNeZeroOfHeight.lean#L37-L46

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UniformizerOfResidueIndep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormByPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GeneratorNeZeroOfHeight
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

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.eq_ratio_smul_on_line {hd : d.AxH 𝒜} {c : ι} {G : WT} {f g : A c} (hf : f ∈ 𝒜 c G) (hg : g ∈ 𝒜 c G)
    (hg0 : g ≠ 0) : f = ratio (Ω := Ω c) f g • g := by sorry
