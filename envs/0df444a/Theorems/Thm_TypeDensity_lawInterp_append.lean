-- Prove2me | Theorems.Thm_TypeDensity_lawInterp_append
-- name    : TypeDensity.lawInterp_append
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:16.754231+00:00
-- url     : https://prove2.me/theorems/327df63b-c123-4687-b4a9-6e9c7a7eb16f
-- title:
--   The interpretation is additive on concatenation.
-- statement:
--   The interpretation is additive on concatenation.
-- source:
--   TypeDensity/Formula/LawAlgebra.lean#L461-L463

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

theorem TypeDensity.lawInterp_append (L M : Law) : lawInterp v (L ++ M) = lawInterp v L + lawInterp v M := by sorry
