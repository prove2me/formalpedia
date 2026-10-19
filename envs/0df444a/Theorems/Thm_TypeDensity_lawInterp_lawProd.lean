-- Prove2me | Theorems.Thm_TypeDensity_lawInterp_lawProd
-- name    : TypeDensity.lawInterp_lawProd
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:52.640765+00:00
-- url     : https://prove2.me/theorems/3c34f606-25b5-4bf2-954f-2fd88f2184a1
-- title:
--   For a multiplicative valuation with `v 1 = 1`, the interpretation is multiplicative on finite products `lawProd`.
-- statement:
--   For a multiplicative valuation with `v 1 = 1`, the interpretation is multiplicative on finite products `lawProd`.
-- source:
--   TypeDensity/Formula/LawAlgebra.lean#L485-L491

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Theorems.Thm_TypeDensity_lawInterp_lawMul
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

theorem TypeDensity.lawInterp_lawProd (hv : ∀ x y, v (.mul x y) = v x * v y) (h1 : v (.const 1) = 1)
    (Ls : List Law) : lawInterp v (lawProd Ls) = (Ls.map (lawInterp v)).prod := by sorry
