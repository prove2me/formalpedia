-- Prove2me | Theorems.Thm_TypeDensity_integral_local_extension_unique_prime
-- name    : TypeDensity.integral_local_extension_unique_prime
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:04.053384+00:00
-- url     : https://prove2.me/theorems/f337b750-3932-4578-af60-840a289af9c8
-- title:
--   For an integral extension of local rings, the maximal ideal of `B` lies over that of `O`, and it is the only prime of `B` lying over it.
-- statement:
--   For an integral extension of local rings, the maximal ideal of `B` lies over that of `O`, and it is the only prime of `B` lying over it.
-- source:
--   TypeDensity/Formula/LawAlgebra.lean#L797-L807

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
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
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.integral_local_extension_unique_prime (O B : Type) [CommRing O] [IsLocalRing O]
    [CommRing B] [IsLocalRing B] [Algebra O B] [Algebra.IsIntegral O B] :
    (IsLocalRing.maximalIdeal B).comap (algebraMap O B) = IsLocalRing.maximalIdeal O ∧
      ∀ Q : Ideal B, Q.IsPrime → Q.comap (algebraMap O B) = IsLocalRing.maximalIdeal O →
        Q = IsLocalRing.maximalIdeal B := by sorry
