-- Prove2me | Theorems.Thm_TypeDensity_unramified_fraction_field_lift
-- name    : TypeDensity.unramified_fraction_field_lift
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:12.230445+00:00
-- url     : https://prove2.me/theorems/db641942-587a-4ba3-9495-1e83b415d8f1
-- title:
--   For an unramified lift `Φ` with `O[X]/(Φ)` a domain, there is a unique ring map of fraction fields extending `O → O[X]/(Φ)`;
-- statement:
--   For an unramified lift `Φ` with `O[X]/(Φ)` a domain, there is a unique ring map of fraction fields extending `O → O[X]/(Φ)`; it is injective and makes the target a field extension of degree `deg Φ`.
-- source:
--   TypeDensity/Unramified/FrobeniusDescent.lean#L229-L273

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
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
open scoped BigOperators ENNReal

theorem TypeDensity.unramified_fraction_field_lift (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ)
    [IsDomain (AdjoinRoot Φ)] :
    ∃ ι : BaseField O →+* BaseField (AdjoinRoot Φ),
      (∀ c : O, ι (algebraMap O (BaseField O) c) =
        algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ)) (algebraMap O (AdjoinRoot Φ) c)) ∧
      Function.Injective ι ∧
      (∀ ι' : BaseField O →+* BaseField (AdjoinRoot Φ),
        (∀ c : O, ι' (algebraMap O (BaseField O) c) =
          algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ)) (algebraMap O (AdjoinRoot Φ) c)) →
        ι' = ι) ∧
      (letI := ι.toAlgebra; Module.Finite (BaseField O) (BaseField (AdjoinRoot Φ)) ∧
        Module.finrank (BaseField O) (BaseField (AdjoinRoot Φ)) = Φ.natDegree) := by sorry
