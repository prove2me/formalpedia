-- Prove2me | Theorems.Thm_TypeDensity_recipSer_recipSer
-- name    : TypeDensity.recipSer_recipSer
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:44:08.825655+00:00
-- url     : https://prove2.me/theorems/e1b43682-8821-4812-8713-aba784a6e318
-- title:
--   `recipSer` is an involution.
-- statement:
--   `recipSer` is an involution.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L581-L583

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_recipCoef_recipCoef
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

theorem TypeDensity.recipSer_recipSer (f : Ser) : recipSer (recipSer f) = f := by sorry
