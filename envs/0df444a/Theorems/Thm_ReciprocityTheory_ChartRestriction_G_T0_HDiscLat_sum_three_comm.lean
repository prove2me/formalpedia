-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HDiscLat_sum_three_comm
-- name    : ReciprocityTheory.ChartRestriction.G.T0.HDiscLat.sum_three_comm
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:36:47.561986+00:00
-- url     : https://prove2.me/theorems/3ab54a6b-8c15-53d3-903d-4be1ac9459c6
-- title:
--   HDisc Lat: sum three comm
-- statement:
--   The HDisc Lat construction uses the sum three comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HDiscAB.lean#L32-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HDiscAB.lean#L32-L38

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

theorem ReciprocityTheory.ChartRestriction.G.T0.HDiscLat.sum_three_comm {α β γ M : Type*} [AddCommMonoid M] (s : Finset α) (t : Finset β) (u : Finset γ)
    (f : α → β → γ → M) :
    ∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, f a b c = ∑ c ∈ u, ∑ b ∈ t, ∑ a ∈ s, f a b c := by sorry
