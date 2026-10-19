-- Prove2me | Theorems.Thm_TypeDensity_polynomial_type_mul_coprime
-- name    : TypeDensity.polynomial_type_mul_coprime
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:09.882056+00:00
-- url     : https://prove2.me/theorems/6cde03ae-1c3c-43b2-bf2f-4bd5cc61f055
-- title:
--   The polynomial type of a product of coprime polynomials is the sum of their types.
-- statement:
--   The polynomial type of a product of coprime polynomials is the sum of their types.
-- source:
--   TypeDensity/Unramified/PolynomialTypes.lean#L124-L142

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

theorem TypeDensity.polynomial_type_mul_coprime (O : Type) [CommRing O] [IsDomain O]
    (G H : Polynomial (BaseField O)) (σ τ : FactorType) (hG : HasPolynomialTypeF O G σ)
    (hH : HasPolynomialTypeF O H τ) (hc : IsCoprime G H) :
    HasPolynomialTypeF O (G * H) (σ + τ) := by sorry
