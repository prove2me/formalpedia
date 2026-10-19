-- Prove2me | Theorems.Thm_TypeDensity_exceptional_line_equiv_chart_exceptional
-- name    : TypeDensity.exceptional_line_equiv_chart_exceptional
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:17.945781+00:00
-- url     : https://prove2.me/theorems/675c7d75-f6ca-4a3b-880b-2741c48d8a48
-- title:
--   The `t`-chart modulo its exceptional ideal is `(R/(t, x))[Z]`.
-- statement:
--   The `t`-chart modulo its exceptional ideal is `(R/(t, x))[Z]`.
-- source:
--   TypeDensity/Blowup/CurveOrders.lean#L435-L444

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Definitions.Def_TypeDensity_Formula_FiniteFieldCounts
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Blowup_Directions
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Blowup_Charts
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_exceptional_chart_is_affine_line
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
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.PicardGroup
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.exceptional_line_equiv_chart_exceptional (R : Type) [CommRing R] (t x : R) :
    ∃ e : (BlowupChart R t x ⧸ chartExceptional R t x) ≃+* Polynomial
        (R ⧸ Ideal.span ({t,x} : Set R)), (∀ r : R, e (Ideal.Quotient.mk (chartExceptional R t x)
        (chartBase R t x r)) = Polynomial.C (Ideal.Quotient.mk (Ideal.span ({t,x} : Set R)) r)) ∧ e
        (Ideal.Quotient.mk (chartExceptional R t x) (chartSlope R t x)) = Polynomial.X := by sorry
