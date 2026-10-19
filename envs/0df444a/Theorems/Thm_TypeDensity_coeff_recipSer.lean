-- Prove2me | Theorems.Thm_TypeDensity_coeff_recipSer
-- name    : TypeDensity.coeff_recipSer
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:55.128644+00:00
-- url     : https://prove2.me/theorems/e0965e34-37d4-4261-87e7-b4418b86f522
-- title:
--   `recipSer` acts coefficientwise: `[xⁿ] fᵛ = v([xⁿ] f)`.
-- statement:
--   `recipSer` acts coefficientwise: `[xⁿ] fᵛ = v([xⁿ] f)`.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L561-L564

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

theorem TypeDensity.coeff_recipSer (f : Ser) (n : ℕ) :
    PowerSeries.coeff n (recipSer f) = recipCoef (PowerSeries.coeff n f) := by sorry
