-- Prove2me | Theorems.Thm_TypeDensity_recipCoef_single
-- name    : TypeDensity.recipCoef_single
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:50.773813+00:00
-- url     : https://prove2.me/theorems/f3a3a6db-1196-40b5-a7c6-74d6de42b58f
-- title:
--   `v` on a monomial acts on the coefficient only.
-- statement:
--   `v` on a monomial acts on the coefficient only.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L66-L69

import Definitions.Def_TypeDensity_Basic
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
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Log
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.recipCoef_single (σ : FactorType) (f : RatFunc ℚ) :
    recipCoef (AddMonoidAlgebra.single σ f) = AddMonoidAlgebra.single σ (recipRat f) := by sorry
