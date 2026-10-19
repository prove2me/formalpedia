-- Prove2me | Theorems.Thm_TypeDensity_residue_ideal_has_fixed_generator_lift
-- name    : TypeDensity.residue_ideal_has_fixed_generator_lift
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:00:52.975975+00:00
-- url     : https://prove2.me/theorems/37da8030-07da-4321-98b9-5c3b3805df90
-- title:
--   Every ideal in the residue cell of a regular `f` has a generator of the form `f + π h`.
-- statement:
--   Every ideal in the residue cell of a regular `f` has a generator of the form `f + π h`.
-- source:
--   TypeDensity/Measure/PrimitiveLocus.lean#L124-L145

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Theorems.Thm_TypeDensity_regular_principal_generators_associated
import Theorems.Thm_TypeDensity_units_lift_from_local_quotient
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
import Mathlib.RingTheory.Henselian
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms
set_option autoImplicit false

open TypeDensity
open MeasureTheory
open scoped BigOperators ENNReal

theorem TypeDensity.residue_ideal_has_fixed_generator_lift (R : Type) [CommRing R] [IsLocalRing R] (pi f : R)
    (hp : pi ∈ IsLocalRing.maximalIdeal R)
    (hf : Function.Injective
      (fun x : R ⧸ Ideal.span {pi} => x * Ideal.Quotient.mk (Ideal.span {pi}) f))
    (J : Ideal R) (hJ : J ∈ residueIdealCell pi f) :
    ∃ h : R, J = Ideal.span {f + pi*h} := by sorry
