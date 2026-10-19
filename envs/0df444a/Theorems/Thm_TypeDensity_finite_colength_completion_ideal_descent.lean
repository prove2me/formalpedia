-- Prove2me | Theorems.Thm_TypeDensity_finite_colength_completion_ideal_descent
-- name    : TypeDensity.finite_colength_completion_ideal_descent
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:31.354457+00:00
-- url     : https://prove2.me/theorems/7e50d1ef-1172-44bd-8b7e-ef556cefdad2
-- title:
--   An ideal `J` of the completion `Â` containing `(m Â)^L` is extended from its contraction to `A`.
-- statement:
--   An ideal `J` of the completion `Â` containing `(m Â)^L` is extended from its contraction to `A`.
-- source:
--   TypeDensity/Unramified/LocalDescent.lean#L134-L153

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Blowup_Directions
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Blowup_Charts
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Theorems.Thm_TypeDensity_local_completion_finite_quotient
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

theorem TypeDensity.finite_colength_completion_ideal_descent (A : Type) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (L : ℕ) (J : Ideal (LocalCompletion A))
    (hJ : ((IsLocalRing.maximalIdeal A).map (localCompletionMap A)) ^ L ≤ J) :
    (J.comap (localCompletionMap A)).map (localCompletionMap A) = J := by sorry
