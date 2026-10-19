-- Prove2me | Theorems.Thm_TypeDensity_integral_closure_algEquiv
-- name    : TypeDensity.integral_closure_algEquiv
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:08.456616+00:00
-- url     : https://prove2.me/theorems/9819bc77-2362-4e3b-a7ee-1cb7bdf24102
-- title:
--   An `O`-algebra isomorphism `L ≃ L'` restricts to the integral closures of `O`.
-- statement:
--   An `O`-algebra isomorphism `L ≃ L'` restricts to the integral closures of `O`.
-- source:
--   TypeDensity/Algebra/AlgebraType.lean#L447-L453

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
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
set_option autoImplicit false

open TypeDensity
open scoped TensorProduct
open Polynomial IsLocalRing

theorem TypeDensity.integral_closure_algEquiv (O L L' : Type) [CommRing O] [CommRing L] [CommRing L']
    [Algebra O L] [Algebra O L'] (e : L ≃ₐ[O] L') :
    ∃ φ : integralClosure O L ≃ₐ[O] integralClosure O L',
      ∀ x : integralClosure O L, (φ x : L') = e x := by sorry
