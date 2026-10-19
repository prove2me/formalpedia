-- Prove2me | Theorems.Thm_TypeDensity_lawInterp_coeff
-- name    : TypeDensity.lawInterp_coeff
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:00.536494+00:00
-- url     : https://prove2.me/theorems/1ba4e772-b253-4497-adf7-163a66c0ea8a
-- title:
--   The coefficients of the interpretation: the sum of the values of the matching entries.
-- statement:
--   The coefficients of the interpretation are the sum of the values of the matching entries.
-- source:
--   TypeDensity/Formula/LawAlgebra.lean#L493-L498

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

theorem TypeDensity.lawInterp_coeff (L : Law) (σ : FactorType) :
    (lawInterp v L).coeff σ = (L.map fun z ↦ if z.1 = σ then v z.2 else 0).sum := by sorry
