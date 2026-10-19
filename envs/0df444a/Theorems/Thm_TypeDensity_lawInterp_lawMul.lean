-- Prove2me | Theorems.Thm_TypeDensity_lawInterp_lawMul
-- name    : TypeDensity.lawInterp_lawMul
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:02.855988+00:00
-- url     : https://prove2.me/theorems/e7a51e85-e5bd-4668-9308-7886c4b6db72
-- title:
--   For a multiplicative valuation, the interpretation is multiplicative on `lawMul`.
-- statement:
--   For a multiplicative valuation, the interpretation is multiplicative on `lawMul`.
-- source:
--   TypeDensity/Formula/LawAlgebra.lean#L471-L476

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

theorem TypeDensity.lawInterp_lawMul (hv : ∀ x y, v (.mul x y) = v x * v y) (L M : Law) :
    lawInterp v (lawMul L M) = lawInterp v L * lawInterp v M := by sorry
