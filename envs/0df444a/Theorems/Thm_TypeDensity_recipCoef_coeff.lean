-- Prove2me | Theorems.Thm_TypeDensity_recipCoef_coeff
-- name    : TypeDensity.recipCoef_coeff
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:53.862985+00:00
-- url     : https://prove2.me/theorems/df59de6c-a013-49ac-8f52-03719d7fb713
-- title:
--   `v` on coefficients: `(v x)_σ = v(x_σ)`.
-- statement:
--   `v` on coefficients: `(v x)_σ = v(x_σ)`.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L80-L83

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

theorem TypeDensity.recipCoef_coeff (x : Coef) (σ : FactorType) :
    (recipCoef x).coeff σ = recipRat (x.coeff σ) := by sorry
