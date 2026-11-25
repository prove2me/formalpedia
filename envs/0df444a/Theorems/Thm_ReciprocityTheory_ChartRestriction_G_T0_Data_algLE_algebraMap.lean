-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_algLE_algebraMap
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.algLE_algebraMap
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:57:23.80986+00:00
-- url     : https://prove2.me/theorems/58479a98-4d45-51a7-8d99-6dd81bd512ea
-- title:
--   Data: alg LE algebra Map
-- statement:
--   The Data construction uses the alg LE algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FracFieldPositiveRowsOmega.lean#L157-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FracFieldPositiveRowsOmega.lean#L157-L159

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OffBaseSubstitution
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FracFieldPositiveRowsOmega
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

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.algLE_algebraMap (h : d.S1) (c : ι) (p : d.PolyRingPositiveRowsBase) :
    letI := d.algLE h c
    algebraMap d.FracFieldPositiveRowsBase (d.FracFieldPositiveRowsOmega c) (algebraMap d.PolyRingPositiveRowsBase d.FracFieldPositiveRowsBase p) = d.psiE c p := by sorry
