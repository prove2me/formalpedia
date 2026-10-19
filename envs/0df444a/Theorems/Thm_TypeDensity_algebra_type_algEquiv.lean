-- Prove2me | Theorems.Thm_TypeDensity_algebra_type_algEquiv
-- name    : TypeDensity.algebra_type_algEquiv
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:42.48589+00:00
-- url     : https://prove2.me/theorems/e73064db-edcd-4aa0-a7ea-3e985e38cfca
-- title:
--   Algebra types are invariant under `O`-algebra isomorphism.
-- statement:
--   Algebra types are invariant under `O`-algebra isomorphism.
-- source:
--   TypeDensity/Algebra/AlgebraType.lean#L409-L415

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

theorem TypeDensity.algebra_type_algEquiv (O : Type) [CommRing O] [IsDomain O] (B B' : Type) [CommRing B]
    [CommRing B'] [Algebra O B] [Algebra O B'] (e : B ≃ₐ[O] B') (σ : FactorType)
    (h : HasAlgebraType O B σ) : HasAlgebraType O B' σ := by sorry
