-- Prove2me | Theorems.Thm_TypeDensity_closure_finite_ascent
-- name    : TypeDensity.closure_finite_ascent
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:05.623977+00:00
-- url     : https://prove2.me/theorems/1e2dd063-c3c2-4826-845c-3eddf2b53d43
-- title:
--   Closure finiteness ascends along a finite extension `O → Oδ` acting on the same ring.
-- statement:
--   Closure finiteness ascends along a finite extension `O → Oδ` acting on the same ring.
-- source:
--   TypeDensity/Algebra/AlgebraType.lean#L143-L148

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

theorem TypeDensity.closure_finite_ascent (O Oδ L : Type) [CommRing O] [CommRing Oδ] [Algebra O Oδ]
    [Module.Finite O Oδ] [CommRing L] [Algebra O L] [Algebra Oδ L] [IsScalarTower O Oδ L]
    (h : Module.Finite O (integralClosure O L)) : Module.Finite Oδ (integralClosure Oδ L) := by sorry
