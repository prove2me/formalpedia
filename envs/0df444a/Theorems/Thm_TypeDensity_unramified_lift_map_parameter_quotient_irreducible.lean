-- Prove2me | Theorems.Thm_TypeDensity_unramified_lift_map_parameter_quotient_irreducible
-- name    : TypeDensity.unramified_lift_map_parameter_quotient_irreducible
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:29.175182+00:00
-- url     : https://prove2.me/theorems/e744dae5-8605-4770-8ec6-5e32cddd3d04
-- title:
--   The reduction of an unramified lift `Φ` to the quotient of the concrete surface by its parameter ideal `(t, x)` is irreducible.
-- statement:
--   The reduction of an unramified lift `Φ` to the quotient of the concrete surface by its parameter ideal `(t, x)` is irreducible.
-- source:
--   TypeDensity/Surfaces/Completeness.lean#L253-L272

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_concrete_surface_quotient_parameters_equiv
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
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.TotallySplit
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.unramified_lift_map_parameter_quotient_irreducible (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ)
    (ha : 0 < a) (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) :
    Irreducible (Φ.map ((Ideal.Quotient.mk (Ideal.span ({surfaceT O pi u a b,
      surfaceX O pi u a b} : Set (ConcreteSurface O pi u a b)))).comp
        (algebraMap O (ConcreteSurface O pi u a b)))) := by sorry
