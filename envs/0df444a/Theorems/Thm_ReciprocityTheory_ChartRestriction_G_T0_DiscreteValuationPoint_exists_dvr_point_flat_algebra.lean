-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_DiscreteValuationPoint_exists_dvr_point_flat_algebra
-- name    : ReciprocityTheory.ChartRestriction.G.T0.DiscreteValuationPoint.exists_dvr_point_flat_algebra
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:36:01.738442+00:00
-- url     : https://prove2.me/theorems/32fe6b60-1925-4c85-adbe-718a31f80395
-- title:
--   Discrete Valuation Point: exists dvr point flat algebra
-- statement:
--   The Discrete Valuation Point construction uses the exists dvr point flat algebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/DiscreteValuationPoint.lean#L290-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/DiscreteValuationPoint.lean#L290-L311

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_DimensionQuotientBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_PrimeAvoidanceFibre
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_DiscreteValuationPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.DiscreteValuationPoint
open IsLocalRing

theorem ReciprocityTheory.ChartRestriction.G.T0.DiscreteValuationPoint.exists_dvr_point_flat_algebra {O B : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CharZero O]
    [CommRing B] [IsDomain B] [Algebra O B] [Algebra.FiniteType O B] [Module.Flat O B]
    (hsp : Ideal.map (algebraMap O B) (maximalIdeal O) ≠ ⊤) (e : B) (he : e ≠ 0) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Algebra O V)
      (_ : Module.Finite O V) (φ : B →ₐ[O] V), φ e ≠ 0 := by sorry
