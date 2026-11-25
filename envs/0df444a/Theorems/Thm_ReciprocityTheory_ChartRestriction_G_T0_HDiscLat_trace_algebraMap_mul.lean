-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HDiscLat_trace_algebraMap_mul
-- name    : ReciprocityTheory.ChartRestriction.G.T0.HDiscLat.trace_algebraMap_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:37:10.246444+00:00
-- url     : https://prove2.me/theorems/cebbff5b-ed16-4e23-95b8-3e2fedb6b2f3
-- title:
--   HDisc Lat: trace algebra Map mul
-- statement:
--   The HDisc Lat construction uses the trace algebra Map mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HDiscAB.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HDiscAB.lean#L17-L20

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.HDiscLat
open Module
variable {R F : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field F]
  [Algebra R F] [IsFractionRing R F]
  {ι : Type} [Fintype ι] [DecidableEq ι] {L : ι → Type} [∀ c, Field (L c)] [∀ c, Algebra F (L c)]
  [∀ c, FiniteDimensional F (L c)] [∀ c, Algebra.IsSeparable F (L c)] [∀ c, Algebra R (L c)]
  [∀ c, IsScalarTower R F (L c)]
omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R F] [Fintype ι] [DecidableEq ι]
  [∀ c, FiniteDimensional F (L c)] [∀ c, Algebra.IsSeparable F (L c)]

theorem ReciprocityTheory.ChartRestriction.G.T0.HDiscLat.trace_algebraMap_mul (c : ι) (r : R) (z : L c) :
    Algebra.trace F (L c) (algebraMap R (L c) r * z) =
      algebraMap R F r * Algebra.trace F (L c) z := by sorry
