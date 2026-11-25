-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_av_point
-- name    : ReciprocityTheory.ChartRestriction.G.T0.av_point
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:30:59.04063+00:00
-- url     : https://prove2.me/theorems/29f98132-dcfe-4aae-8b88-3d7d17fb9c5f
-- title:
--   T0: av point
-- statement:
--   The T0 construction uses the av point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/RegAVpt.lean#L8-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/RegAVpt.lean#L8-L14

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_DiscreteValuationPoint
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RegAVpt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open IsLocalRing

theorem ReciprocityTheory.ChartRestriction.G.T0.av_point {O B : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CharZero O]
    [CommRing B] [IsDomain B] [Algebra O B] [Algebra.FiniteType O B] [Module.Flat O B]
    (hsp : Ideal.map (algebraMap O B) (maximalIdeal O) ≠ ⊤) (e : B) (he : e ≠ 0) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Algebra O V)
      (_ : Module.Finite O V) (φ : B →ₐ[O] V), φ e ≠ 0 := by sorry
