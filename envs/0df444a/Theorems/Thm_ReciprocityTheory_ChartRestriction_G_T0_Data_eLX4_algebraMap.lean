-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_eLX4_algebraMap
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.eLX4_algebraMap
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:56:25.634386+00:00
-- url     : https://prove2.me/theorems/463f574a-3dfb-537a-9057-289d52c8c47f
-- title:
--   Data: e LX4 algebra Map
-- statement:
--   The Data construction uses the e LX4 algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FracFieldPositiveRowsOmega.lean#L37-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FracFieldPositiveRowsOmega.lean#L37-L42

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

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.eLX4_algebraMap (P : KTp K d.D d.N) :
    d.eLX4 (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) P) =
      FractionFieldVariableLift.toFracY d.PolyRingPositiveRowsBase (Fin (d.N + 1)) (FractionFieldVariableLift.hL K d.D d.N P) := by sorry
