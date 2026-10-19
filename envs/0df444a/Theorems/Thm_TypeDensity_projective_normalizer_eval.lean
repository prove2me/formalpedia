-- Prove2me | Theorems.Thm_TypeDensity_projective_normalizer_eval
-- name    : TypeDensity.projective_normalizer_eval
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:06.609018+00:00
-- url     : https://prove2.me/theorems/7d89276f-8c41-44be-9c8a-84813f08b382
-- title:
--   The projective normalizer evaluates to `1 + q + ⋯ + q^n`, and `(1 + ⋯ + q^n)(q − 1) = q^(n+1) − 1`.
-- statement:
--   The projective normalizer evaluates to `1 + q + ⋯ + q^n`, and `(1 + ⋯ + q^n)(q − 1) = q^(n+1) − 1`.
-- source:
--   TypeDensity/Unramified/PolynomialTypes.lean#L769-L792

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
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
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms
set_option autoImplicit false

open TypeDensity
open scoped ENNReal

theorem TypeDensity.projective_normalizer_eval (q : ℚ) (n : ℕ) :
    (projectiveNormalizer n).eval q = ∑ i ∈ Finset.range (n+1), q ^ i ∧
      (∑ i ∈ Finset.range (n+1), q ^ i) * (q - 1) = q ^ (n+1) - 1 := by sorry
