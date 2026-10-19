-- Prove2me | Theorems.Thm_TypeDensity_curve_ideal_lattice_eq_kernels
-- name    : TypeDensity.curve_ideal_lattice_eq_kernels
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:30:42.410522+00:00
-- url     : https://prove2.me/theorems/5b686da5-123d-4673-8013-200e4f771411
-- title:
--   If the glued generators generate the level kernels of the curve data, then the curve ideals on the two charts are the kernels of the finitely supported local data.
-- statement:
--   If the glued generators generate the level kernels of the curve data, then the curve ideals on the two charts are the kernels of the finitely supported local data.
-- source:
--   TypeDensity/Blowup/CurveOrders.lean#L68-L96

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

theorem TypeDensity.curve_ideal_lattice_eq_kernels (R : Type) [CommRing R] (t x : R)
    [(Ideal.span ({t,x} : Set R)).IsMaximal] [IsNoetherianRing (BlowupChart R t x)]
    [IsNoetherianRing (BlowupChart R x t)] (beta : BlowupRestriction R t x)
    (D : TwoChartCurveData R t x beta) (d : ℕ) (G : GluedGenerators R t x beta d)
    (hG : ∀ j : ℕ, Ideal.span {Ideal.Quotient.mk ((chartExceptional R t x)^j) (G.left j)} =
    leftLevelKernel D j ∧ Ideal.span {Ideal.Quotient.mk ((chartExceptional R x t)^j) (G.right j)} =
    rightLevelKernel D j) (j : ℕ) :
    leftCurveIdeal R t x beta G j = leftKernel D j ∧ rightCurveIdeal R t x beta G j = rightKernel D
        j := by sorry
