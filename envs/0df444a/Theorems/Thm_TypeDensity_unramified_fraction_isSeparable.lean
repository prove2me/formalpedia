-- Prove2me | Theorems.Thm_TypeDensity_unramified_fraction_isSeparable
-- name    : TypeDensity.unramified_fraction_isSeparable
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:14:36.450748+00:00
-- url     : https://prove2.me/theorems/335e2765-d111-40fa-b7e3-33023988de91
-- title:
--   The unramified fraction-field extension `Kδ/K` is finite and separable (it is Galois: the Frobenius `τ 1` already has fixed field `K`).
-- statement:
--   The unramified fraction-field extension `Kδ/K` is finite and separable (it is Galois: the Frobenius `τ 1` already has fixed field `K`).
-- source:
--   TypeDensity/Unramified/DescentTypes.lean#L197-L216

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_frobenius_fraction_extension
import Theorems.Thm_TypeDensity_unramified_fraction_field_lift
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
variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
  (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) [IsDomain (AdjoinRoot Φ)]
  (ι : BaseField O →+* BaseField (AdjoinRoot Φ))
  (hι : ∀ c : O, ι (algebraMap O (BaseField O) c) =
    algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ)) (algebraMap O (AdjoinRoot Φ) c))
include hΦ hι

theorem TypeDensity.unramified_fraction_isSeparable :
    letI := ι.toAlgebra
    FiniteDimensional (BaseField O) (BaseField (AdjoinRoot Φ)) ∧
      Algebra.IsSeparable (BaseField O) (BaseField (AdjoinRoot Φ)) := by sorry
