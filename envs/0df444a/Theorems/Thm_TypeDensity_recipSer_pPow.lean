-- Prove2me | Theorems.Thm_TypeDensity_recipSer_pPow
-- name    : TypeDensity.recipSer_pPow
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:44:44.879522+00:00
-- url     : https://prove2.me/theorems/55b6de44-8a96-4bec-a262-37f11ec7f74e
-- title:
--   The reciprocal substitution commutes with the plethystic powers, twisting the exponent by `q ↦ q⁻¹`: `P_w(g)ᵛ = P_{v(w)}(gᵛ)` for `g(0) = 1`.
-- statement:
--   The reciprocal substitution commutes with the plethystic powers, twisting the exponent by `q ↦ q⁻¹`: `P_w(g)ᵛ = P_{v(w)}(gᵛ)` for `g(0) = 1`.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L803-L824

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_recipCoef_scalar
import Theorems.Thm_TypeDensity_recipCoef_adamsCoef
import Theorems.Thm_TypeDensity_constantCoeff_plethSum
import Theorems.Thm_TypeDensity_coeff_recipSer
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

theorem TypeDensity.recipSer_pPow (w : RatFunc ℚ) (g : Ser) (hg : PowerSeries.constantCoeff g = 1) :
    recipSer (pPow w g) = pPow (recipRat w) (recipSer g) := by sorry
