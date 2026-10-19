-- Prove2me | Theorems.Thm_TypeDensity_lawInterp_lawScale
-- name    : TypeDensity.lawInterp_lawScale
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:10.066174+00:00
-- url     : https://prove2.me/theorems/f73ae84b-2c5c-490c-8138-c86d29f57abb
-- title:
--   For a multiplicative valuation, the interpretation turns `lawScale x` into multiplication by the scalar `v x`.
-- statement:
--   For a multiplicative valuation, the interpretation turns `lawScale x` into multiplication by the scalar `v x`.
-- source:
--   TypeDensity/Formula/LawAlgebra.lean#L478-L483

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

theorem TypeDensity.lawInterp_lawScale (hv : ∀ x y, v (.mul x y) = v x * v y) (x : Expr) (L : Law) :
    lawInterp v (lawScale x L) = AddMonoidAlgebra.single 0 (v x) * lawInterp v L := by sorry
