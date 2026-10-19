-- Prove2me | Theorems.Thm_TypeDensity_law_coeff_mul
-- name    : TypeDensity.law_coeff_mul
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:00:35.317172+00:00
-- url     : https://prove2.me/theorems/413456d0-2032-4be9-a5d3-44116d9aac67
-- title:
--   Coefficient formula for a product of two laws: a convolution over the types of `L`.
-- statement:
--   The coefficients of a product of two laws are given by a convolution over the types of `L`.
-- source:
--   TypeDensity/Formula/LawAlgebra.lean#L529-L547

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Theorems.Thm_TypeDensity_lawInterp_lawMul
import Theorems.Thm_TypeDensity_lawInterp_coeff
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

theorem TypeDensity.law_coeff_mul (L M : Law) (σ : FactorType) (q : ℚ) :
    (lawCoeff (lawMul L M) σ).eval q = ∑ τ ∈ (L.map Prod.fst).toFinset,
      (if τ ≤ σ then (lawCoeff L τ).eval q * (lawCoeff M (σ - τ)).eval q else 0) := by sorry
