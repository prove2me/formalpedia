-- Prove2me | Theorems.Thm_TypeDensity_map_maximalIdeal_localCompletion_transport
-- name    : TypeDensity.map_maximalIdeal_localCompletion_transport
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:36.563812+00:00
-- url     : https://prove2.me/theorems/3878f63a-a423-4ed9-95a7-745984326ea0
-- title:
--   A ring isomorphism `Θ : (B_Q)^ ≃ (A_P)^` compatible with `f : A → B` carries the extension of `f(P)` to the maximal ideal of `(A_P)^`.
-- statement:
--   A ring isomorphism `Θ : (B_Q)^ ≃ (A_P)^` compatible with `f : A → B` carries the extension of `f(P)` to the maximal ideal of `(A_P)^`.
-- source:
--   TypeDensity/Blowup/CurveSections.lean#L928-L937

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
import Definitions.Def_TypeDensity_Surfaces_TruncatedSeries
import Theorems.Thm_TypeDensity_map_maximalIdeal_localCompletion
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

theorem TypeDensity.map_maximalIdeal_localCompletion_transport {A B : Type} [CommRing A] [CommRing B]
    (f : A →+* B) (P : Ideal A) (Q : Ideal B) [P.IsPrime] [Q.IsPrime]
    (Θ : CompletedLocalAt B Q ≃+* CompletedLocalAt A P)
    (hΘ : ∀ a, Θ (completedPointMap B Q (f a)) = completedPointMap A P a) :
    ((P.map f).map (completedPointMap B Q)).map (Θ : _ →+* _) =
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)).map (localCompletionMap _) := by sorry
