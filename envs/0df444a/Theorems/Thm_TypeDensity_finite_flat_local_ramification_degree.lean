-- Prove2me | Theorems.Thm_TypeDensity_finite_flat_local_ramification_degree
-- name    : TypeDensity.finite_flat_local_ramification_degree
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:00:33.35433+00:00
-- url     : https://prove2.me/theorems/d78ad732-6344-4798-8e95-37422182abe4
-- title:
--   For a finite flat extension of local rings `O → B`, `e · f = [B : O]`.
-- statement:
--   For a finite flat extension of local rings `O → B`, `e · f = [B : O]`.
-- source:
--   TypeDensity/Formula/LawAlgebra.lean#L809-L825

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Theorems.Thm_TypeDensity_integral_local_extension_unique_prime
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

theorem TypeDensity.finite_flat_local_ramification_degree (O B : Type) [CommRing O] [IsDomain O]
    [IsLocalRing O] [CommRing B] [IsLocalRing B] [Algebra O B] [Module.Finite O B]
    [Module.Flat O B] :
    (IsLocalRing.maximalIdeal B).ramificationIdx O * (IsLocalRing.maximalIdeal B).inertiaDeg O =
      Module.finrank O B := by sorry
