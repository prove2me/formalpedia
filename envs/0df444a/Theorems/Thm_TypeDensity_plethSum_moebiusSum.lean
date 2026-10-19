-- Prove2me | Theorems.Thm_TypeDensity_plethSum_moebiusSum
-- name    : TypeDensity.plethSum_moebiusSum
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:44:15.731289+00:00
-- url     : https://prove2.me/theorems/49a6815b-77e6-4049-bb0a-b227dcbcadd1
-- title:
--   Möbius inversion: `plethSum (moebiusSum f) = f` for `f(0) = 0`.
-- statement:
--   Möbius inversion: `plethSum (moebiusSum f) = f` for `f(0) = 0`.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L366-L369

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_adamsCoef_one
import Theorems.Thm_TypeDensity_coeff_divisorTransform_comp
import Theorems.Thm_TypeDensity_sum_divisors_moebius
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Log
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.plethSum_moebiusSum (f : Ser) (hf : PowerSeries.constantCoeff f = 0) :
    plethSum (moebiusSum f) = f := by sorry
