-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_fieldEquiv_compat_liftY
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.fieldEquiv_compat_liftY
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:56:26.516261+00:00
-- url     : https://prove2.me/theorems/5cc1c8be-8d74-52dd-a10a-9027203e3ef5
-- title:
--   Data: field Equiv compat lift Y
-- statement:
--   The Data construction uses the field Equiv compat lift Y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FracFieldPositiveRowsOmega.lean#L161-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FracFieldPositiveRowsOmega.lean#L161-L174

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

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.fieldEquiv_compat_liftY (h : d.S1) (c : ι) (q : KTf K d.D d.N) :
    letI := d.algLE h c
    d.eEX4 c (d.KTtoS h c q) = VariableBasisExtension.liftY (L := d.FracFieldPositiveRowsBase) (E := d.FracFieldPositiveRowsOmega c) (σ := Fin (d.N + 1)) (d.eLX4 q) := by sorry
