-- Prove2me | Theorems.Thm_TypeDensity_moebiusSum_plethSum
-- name    : TypeDensity.moebiusSum_plethSum
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:44:27.70569+00:00
-- url     : https://prove2.me/theorems/7922ccfe-97a4-4d24-aa6c-886c3ec575ad
-- title:
--   Möbius inversion: `moebiusSum (plethSum f) = f` for `f(0) = 0`.
-- statement:
--   Möbius inversion: `moebiusSum (plethSum f) = f` for `f(0) = 0`.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L361-L364

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

theorem TypeDensity.moebiusSum_plethSum (f : Ser) (hf : PowerSeries.constantCoeff f = 0) :
    moebiusSum (plethSum f) = f := by sorry
