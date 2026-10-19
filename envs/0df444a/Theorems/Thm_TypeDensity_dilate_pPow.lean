-- Prove2me | Theorems.Thm_TypeDensity_dilate_pPow
-- name    : TypeDensity.dilate_pPow
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:20:03.990676+00:00
-- url     : https://prove2.me/theorems/14a2ff7c-bf1d-48a8-a72d-f0bf4f77cdfe
-- title:
--   The dilation commutes with the plethystic powers `P_w` (for `g(0) = 1`).
-- statement:
--   The dilation commutes with the plethystic powers `P_w` (for `g(0) = 1`).
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L675-L679

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_adamsRat_zpow_X
import Theorems.Thm_TypeDensity_adamsCoef_scalar
import Theorems.Thm_TypeDensity_constantCoeff_plethSum
import Theorems.Thm_TypeDensity_coeff_dilate
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

theorem TypeDensity.dilate_pPow (w : RatFunc ℚ) (g : Ser) (hg : PowerSeries.constantCoeff g = 1) :
    dilate (pPow w g) = pPow w (dilate g) := by sorry
