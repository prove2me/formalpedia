-- Prove2me | Theorems.Thm_TypeDensity_closure_finite_descent
-- name    : TypeDensity.closure_finite_descent
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:06.548475+00:00
-- url     : https://prove2.me/theorems/0820c6ed-748a-4db7-af7a-4a49a6bc80b7
-- title:
--   Closure finiteness descends along a finite extension `O → Oδ`: the two integral closures coincide, and finite over `Oδ` finite over `O` is finite over `O`.
-- statement:
--   Closure finiteness descends along a finite extension `O → Oδ`: the two integral closures coincide, and finite over `Oδ` finite over `O` is finite over `O`.
-- source:
--   TypeDensity/Algebra/AlgebraType.lean#L135-L141

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

theorem TypeDensity.closure_finite_descent (O Oδ L : Type) [CommRing O] [CommRing Oδ] [Algebra O Oδ]
    [Module.Finite O Oδ] [CommRing L] [Algebra O L] [Algebra Oδ L] [IsScalarTower O Oδ L]
    (h : Module.Finite Oδ (integralClosure Oδ L)) : Module.Finite O (integralClosure O L) := by sorry
