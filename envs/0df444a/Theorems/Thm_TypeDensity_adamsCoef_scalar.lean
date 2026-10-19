-- Prove2me | Theorems.Thm_TypeDensity_adamsCoef_scalar
-- name    : TypeDensity.adamsCoef_scalar
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:57.723735+00:00
-- url     : https://prove2.me/theorems/77a52700-362a-4c09-a6be-62eb8ab575fd
-- title:
--   `ψ_δ` on scalars is `q ↦ q^δ`.
-- statement:
--   `ψ_δ` on scalars is `q ↦ q^δ`.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L71-L74

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_adamsCoef_single
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

theorem TypeDensity.adamsCoef_scalar (δ : ℕ) (f : RatFunc ℚ) :
    adamsCoef δ (scalar f) = scalar (adamsRat δ f) := by sorry
