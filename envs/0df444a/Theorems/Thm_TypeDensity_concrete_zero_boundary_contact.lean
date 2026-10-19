-- Prove2me | Theorems.Thm_TypeDensity_concrete_zero_boundary_contact
-- name    : TypeDensity.concrete_zero_boundary_contact
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:26:17.931382+00:00
-- url     : https://prove2.me/theorems/a73397ed-5359-42dc-9dae-eeb666b871fc
-- title:
--   The intersection length of a degree-`d` form with `(X)` on the concrete surface is `d` plus the intersection length of its strict transform with the exceptional divisor at the origin of the left chart
-- statement:
--   The intersection length of a degree-`d` form with `(X)` on the concrete surface is `d` plus the intersection length of its strict transform with the exceptional divisor at the origin of the left chart.
-- source:
--   TypeDensity/Blowup/NilpotentGluing.lean#L1418-L1480

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Definitions.Def_TypeDensity_Formula_FiniteFieldCounts
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Blowup_Directions
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Blowup_Charts
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_residueKillX_apply_ker
import Theorems.Thm_TypeDensity_concrete_surface_quotient_X_equiv
import Theorems.Thm_TypeDensity_length_quotient_comap_of_surjective
import Theorems.Thm_TypeDensity_surjective_ker_comp_quotient_equiv
import Theorems.Thm_TypeDensity_t_chart_origin_completion_equiv
import Theorems.Thm_TypeDensity_powerSeries_quotient_length_eq_order
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.PicardGroup
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.Algebra.Group.NatPowAssoc
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.concrete_zero_boundary_contact (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (d : ℕ) (f : (ConcreteSurface O pi u a b))
    (c : Fin (d + 1) → (ConcreteSurface O pi u a b))
    (hc : f = ∑ i : Fin (d + 1), c i * (surfaceT O pi u a b) ^ (d - i.val) *
      (surfaceX O pi u a b) ^ i.val)
    (P : Ideal ((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)))) [P.IsPrime]
    (hP : P = Ideal.span {(chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) (surfaceT O pi u a b), ((chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)))}) :
    Module.length (ConcreteSurface O pi u a b)
    ((ConcreteSurface O pi u a b) ⧸ (Ideal.span {f} ⊔ Ideal.span {(surfaceX O pi u a b)})) =
    (d : ℕ∞) + Module.length (CompletedLocalAt ((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) P)
    (CompletedLocalAt ((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) P ⧸
      (Ideal.span {completedPointMap ((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) P
          (∑ i : Fin (d+1), algebraMap (ConcreteSurface O pi u a b) ((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) (c i) *
            ((chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)))^i.val)} ⊔
        Ideal.span {completedPointMap ((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) P ((chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)))})) := by sorry
