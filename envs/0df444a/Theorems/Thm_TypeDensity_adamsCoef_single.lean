-- Prove2me | Theorems.Thm_TypeDensity_adamsCoef_single
-- name    : TypeDensity.adamsCoef_single
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:56.436182+00:00
-- url     : https://prove2.me/theorems/5e0e5193-1673-402f-82e4-f9e99c6dbf50
-- title:
--   `ψ_δ` on a monomial: `q ↦ q^δ` on the coefficient and `Z_{e,f} ↦ Z_{e,δf}` on the type.
-- statement:
--   `ψ_δ` on a monomial: `q ↦ q^δ` on the coefficient and `Z_{e,f} ↦ Z_{e,δf}` on the type.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L59-L64

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

theorem TypeDensity.adamsCoef_single (δ : ℕ) (σ : FactorType) (f : RatFunc ℚ) :
    adamsCoef δ (AddMonoidAlgebra.single σ f) =
      AddMonoidAlgebra.single (scaleType δ σ) (adamsRat δ f) := by sorry
