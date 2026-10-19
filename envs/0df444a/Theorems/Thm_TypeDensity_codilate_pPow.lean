-- Prove2me | Theorems.Thm_TypeDensity_codilate_pPow
-- name    : TypeDensity.codilate_pPow
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:32:43.540481+00:00
-- url     : https://prove2.me/theorems/ab57fd9e-d09f-4e3e-bc99-38c2403ab687
-- title:
--   The inverse dilation commutes with the plethystic powers `P_w` (for `g(0) = 1`).
-- statement:
--   The inverse dilation commutes with the plethystic powers `P_w` (for `g(0) = 1`).
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L681-L685

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_qpow_zero
import Theorems.Thm_TypeDensity_coeff_codilate
import Theorems.Thm_TypeDensity_codilate_dilate
import Theorems.Thm_TypeDensity_dilate_codilate
import Theorems.Thm_TypeDensity_dilate_pPow
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

theorem TypeDensity.codilate_pPow (w : RatFunc ℚ) (g : Ser) (hg : PowerSeries.constantCoeff g = 1) :
    codilate (pPow w g) = pPow w (codilate g) := by sorry
