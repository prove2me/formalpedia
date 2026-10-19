-- Prove2me | Theorems.Thm_TypeDensity_terminal_curve_order_local_principal
-- name    : TypeDensity.terminal_curve_order_local_principal
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:38:18.790603+00:00
-- url     : https://prove2.me/theorems/b0db73a5-df56-41f0-a9df-422d93add2db
-- title:
--   For `J = (f)` in the terminal state `single a 1`: `(f, t)` is the maximal ideal, and `R/J` is a Noetherian local ring with principal maximal ideal `(t)`, finite free of rank `a` over `O`.
-- statement:
--   For `J = (f)` in the terminal state `single a 1`: `(f, t)` is the maximal ideal, and `R/J` is a Noetherian local ring with principal maximal ideal `(t)`, finite free of rank `a` over `O`.
-- source:
--   TypeDensity/Recursion/ChildMembers.lean#L479-L537

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Blowup_Directions
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Definitions.Def_TypeDensity_Formula_FiniteFieldCounts
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Formula_PatternCounts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Blowup_Charts
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Definitions.Def_TypeDensity_Surfaces_TruncatedSeries
import Definitions.Def_TypeDensity_Blowup_TwoChartCurveData
import Definitions.Def_TypeDensity_Surfaces_ConcreteAtlas
import Definitions.Def_TypeDensity_Recursion_Members
import Definitions.Def_TypeDensity_Measure_MemberCharts
import Definitions.Def_TypeDensity_Recursion_Termination
import Definitions.Def_TypeDensity_Recursion_OrderDefect
import Definitions.Def_TypeDensity_Recursion_ChildMembers
import Theorems.Thm_TypeDensity_surface_state_ideal_proper
import Theorems.Thm_TypeDensity_concrete_surface_single_curve_free
import Theorems.Thm_TypeDensity_concrete_surface_isNoetherianRing
import Theorems.Thm_TypeDensity_concrete_surface_contact_eq_special_fiber_contact
import Theorems.Thm_TypeDensity_concrete_surface_special_fiber_equiv
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal TensorProduct

theorem TypeDensity.terminal_curve_order_local_principal (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a) [IsDomain (ConcreteSurface O pi u a b)]
    [IsRegularLocalRing (ConcreteSurface O pi u a b)]
    (S : SurfaceData O (ConcreteSurface O pi u a b)) (hSpi : S.pi = pi)
    (hSt : S.t = (surfaceT O pi u a b)) (hSx : S.x = (surfaceX O pi u a b)) (hSa : S.a = a)
    (hSb : S.b = b) (J : Ideal (ConcreteSurface O pi u a b))
    (hJ : J ∈ surfaceStateSet O (ConcreteSurface O pi u a b) S (State.single a 1))
    (f : (ConcreteSurface O pi u a b)) (hf : J = Ideal.span {f}) :
    Ideal.span {f} ⊔ Ideal.span {(surfaceT O pi u a b)} = IsLocalRing.maximalIdeal
        (ConcreteSurface O pi u a b) ∧
    (∃ _ : IsLocalRing ((ConcreteSurface O pi u a b) ⧸ J), IsLocalRing.maximalIdeal
        ((ConcreteSurface O pi u a b) ⧸ J) = Ideal.span {(Ideal.Quotient.mk J
        (surfaceT O pi u a b))}) ∧
    IsNoetherianRing ((ConcreteSurface O pi u a b) ⧸ J) ∧
    Module.Free O ((ConcreteSurface O pi u a b) ⧸ J) ∧
    Module.Finite O ((ConcreteSurface O pi u a b) ⧸ J) ∧
    Module.finrank O ((ConcreteSurface O pi u a b) ⧸ J) = a := by sorry
