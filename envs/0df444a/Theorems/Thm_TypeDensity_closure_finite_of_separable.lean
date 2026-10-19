-- Prove2me | Theorems.Thm_TypeDensity_closure_finite_of_separable
-- name    : TypeDensity.closure_finite_of_separable
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:03.727522+00:00
-- url     : https://prove2.me/theorems/81906880-faed-4614-803f-fbd7396acc52
-- title:
--   For `g` irreducible and separable over `Frac O`, the integral closure of `O` in `K[X]/(g)` is a finite `O`-module.
-- statement:
--   For `g` irreducible and separable over `Frac O`, the integral closure of `O` in `K[X]/(g)` is a finite `O`-module.
-- source:
--   TypeDensity/Algebra/AlgebraType.lean#L333-L342

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

theorem TypeDensity.closure_finite_of_separable (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (g : (FractionRing O)[X]) (hirr : Irreducible g)
    (hs : g.Separable) : Module.Finite O (integralClosure O (AdjoinRoot g)) := by sorry
