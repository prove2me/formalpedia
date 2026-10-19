-- Prove2me | Theorems.Thm_TypeDensity_eq_of_mul_derivative_eq_mul
-- name    : TypeDensity.eq_of_mul_derivative_eq_mul
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:32:04.477121+00:00
-- url     : https://prove2.me/theorems/24366182-d67e-4fbc-ba63-a54b1081eb56
-- title:
--   Uniqueness for the linear ODE `g E' = w E` with `g(0) = 1`: a solution is determined by its constant term.
-- statement:
--   Uniqueness for the linear ODE `g E' = w E` with `g(0) = 1`: a solution is determined by its constant term.
-- source:
--   TypeDensity/Reciprocity/Plethysm.lean#L86-L129

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
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
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Log
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.eq_of_mul_derivative_eq_mul (g w E F : Ser) (hg : PowerSeries.constantCoeff g = 1)
    (hE : g * PowerSeries.derivative Coef E = w * E)
    (hF : g * PowerSeries.derivative Coef F = w * F)
    (h0 : PowerSeries.constantCoeff E = PowerSeries.constantCoeff F) :
    E = F := by sorry
