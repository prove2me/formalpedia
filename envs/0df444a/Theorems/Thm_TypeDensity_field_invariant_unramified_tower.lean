-- Prove2me | Theorems.Thm_TypeDensity_field_invariant_unramified_tower
-- name    : TypeDensity.field_invariant_unramified_tower
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:44:17.096753+00:00
-- url     : https://prove2.me/theorems/b57cdb63-c33b-46d9-87fc-27f3b3a363ae
-- title:
--   In an unramified tower `O → Oδ` of degree `δ`, the invariant `(e, f)` of a finite extension `L` over `Oδ` becomes `(e, δ f)` over `O`.
-- statement:
--   In an unramified tower `O → Oδ` of degree `δ`, the invariant `(e, f)` of a finite extension `L` over `Oδ` becomes `(e, δ f)` over `O`.
-- source:
--   TypeDensity/Unramified/DescentTypes.lean#L50-L100

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_algebraMap_injective_of_tower
import Theorems.Thm_TypeDensity_closure_finite_descent
import Theorems.Thm_TypeDensity_dvr_algEquiv_ramification_inertia
import Theorems.Thm_TypeDensity_inertiaDeg_unramified_tower
import Theorems.Thm_TypeDensity_ramificationIdx_unramified_tower
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
open Polynomial

theorem TypeDensity.field_invariant_unramified_tower (O Oδ : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CommRing Oδ] [IsDomain Oδ] [IsDiscreteValuationRing Oδ]
    [Algebra O Oδ] [Module.Finite O Oδ] [Module.Free O Oδ] (δ : ℕ) (hrank : Module.finrank O Oδ = δ)
    (pi : O) (hpi : Irreducible pi) (hpiδ : Irreducible (algebraMap O Oδ pi))
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)] (L : Type)
    [Field L] [Algebra O L] [Algebra Oδ L] [IsScalarTower O Oδ L] [Algebra (BaseField O) L]
    [IsScalarTower O (BaseField O) L] [FiniteDimensional (BaseField O) L] [Algebra (BaseField Oδ) L]
    [IsScalarTower Oδ (BaseField Oδ) L] [FiniteDimensional (BaseField Oδ) L]
    (hfinδ : Module.Finite Oδ (integralClosure Oδ L)) :
    fieldInvariant O L = ((fieldInvariant Oδ L).1, δ * (fieldInvariant Oδ L).2) := by sorry
