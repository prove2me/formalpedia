-- Prove2me | Theorems.Thm_TypeDensity_local_completion_finite_quotient
-- name    : TypeDensity.local_completion_finite_quotient
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:30:27.4472+00:00
-- url     : https://prove2.me/theorems/7f90e9ea-dc82-41b1-99f4-9f06e355dfbf
-- title:
--   For a Noetherian local ring `(A, m)` with completion `Â`, the quotient `Â/(m Â)^L` is `A`-isomorphic to `A/m^L`, compatibly with the maps from `A`.
-- statement:
--   For a Noetherian local ring `(A, m)` with completion `Â`, the quotient `Â/(m Â)^L` is `A`-isomorphic to `A/m^L`, compatibly with the maps from `A`.
-- source:
--   TypeDensity/Unramified/LocalDescent.lean#L94-L118

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Blowup_Directions
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Blowup_Charts
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.PicardGroup
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Completeness
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.local_completion_finite_quotient (A : Type) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (L : ℕ) :
    ∃ E : (LocalCompletion A ⧸ ((IsLocalRing.maximalIdeal A).map (localCompletionMap A))^L) ≃ₐ[A]
      (A ⧸ (IsLocalRing.maximalIdeal A)^L), ∀ a : A,
      E (Ideal.Quotient.mk (((IsLocalRing.maximalIdeal A).map (localCompletionMap A))^L)
        (localCompletionMap A a)) = Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A)^L) a := by sorry
