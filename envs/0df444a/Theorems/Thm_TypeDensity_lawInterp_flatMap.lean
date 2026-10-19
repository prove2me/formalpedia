-- Prove2me | Theorems.Thm_TypeDensity_lawInterp_flatMap
-- name    : TypeDensity.lawInterp_flatMap
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:41.578007+00:00
-- url     : https://prove2.me/theorems/7d86389a-3c3a-4489-b645-16613fc4ab8a
-- title:
--   The interpretation sends a `flatMap` to the sum of the pieces.
-- statement:
--   The interpretation sends a `flatMap` to the sum of the pieces.
-- source:
--   TypeDensity/Formula/LawAlgebra.lean#L465-L469

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
variable {S : Type*} [Semiring S] (v : Expr → S)

theorem TypeDensity.lawInterp_flatMap {α : Type} (xs : List α) (g : α → Law) :
    lawInterp v (xs.flatMap g) = (xs.map fun u ↦ lawInterp v (g u)).sum := by sorry
