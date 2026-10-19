-- Prove2me | Theorems.Thm_TypeDensity_recipSer_gaussPhi
-- name    : TypeDensity.recipSer_gaussPhi
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:21:47.936951+00:00
-- url     : https://prove2.me/theorems/529226a3-6017-4af7-a8a9-2f5777dc1320
-- title:
--   The reciprocal substitution conjugates `Φ` to `Φ⁻¹`.
-- statement:
--   The reciprocal substitution conjugates `Φ` to `Φ⁻¹`.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L689-L693

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_recipRat_X
import Theorems.Thm_TypeDensity_recipCoef_scalar
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

theorem TypeDensity.recipSer_gaussPhi (f : Ser) : recipSer (gaussPhi f) = gaussPhiInv (recipSer f) := by sorry
