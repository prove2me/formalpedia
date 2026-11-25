-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HDiscLat_trace_term
-- name    : ReciprocityTheory.ChartRestriction.G.T0.HDiscLat.trace_term
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:37:13.932597+00:00
-- url     : https://prove2.me/theorems/8342ec9a-d05c-4b16-a485-e955d67886a4
-- title:
--   HDisc Lat: trace term
-- statement:
--   The HDisc Lat construction uses the trace term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HDiscAB.lean#L24-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HDiscAB.lean#L24-L30

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

theorem ReciprocityTheory.ChartRestriction.G.T0.HDiscLat.trace_term (c : ι) (r r' : R) (h x y : L c) :
    Algebra.trace F (L c) (algebraMap R (L c) r * (h * x) * (algebraMap R (L c) r' * (h * y))) =
      algebraMap R F r * Algebra.trace F (L c) (h * h * x * y) * algebraMap R F r' := by sorry
