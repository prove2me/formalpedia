-- Prove2me | Theorems.Thm_TypeDensity_recipCoef_recipCoef
-- name    : TypeDensity.recipCoef_recipCoef
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:32:15.330714+00:00
-- url     : https://prove2.me/theorems/d7df7515-1b2e-4f63-a7ac-89124ce545f1
-- title:
--   `v` is an involution of `Coef`.
-- statement:
--   `v` is an involution of `Coef`.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L90-L93

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_recipRat_recipRat
import Theorems.Thm_TypeDensity_recipCoef_single
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

theorem TypeDensity.recipCoef_recipCoef (x : Coef) : recipCoef (recipCoef x) = x := by sorry
