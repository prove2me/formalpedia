-- Prove2me | Theorems.Thm_TypeDensity_recipSer_dilate
-- name    : TypeDensity.recipSer_dilate
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:20:01.827171+00:00
-- url     : https://prove2.me/theorems/13f321a3-279b-43b5-9326-3de5cd4813ed
-- title:
--   The reciprocal substitution conjugates `S` to `S⁻¹`.
-- statement:
--   The reciprocal substitution conjugates `S` to `S⁻¹`.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L630-L633

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_recipRat_X
import Theorems.Thm_TypeDensity_recipCoef_scalar
import Theorems.Thm_TypeDensity_coeff_recipSer
import Theorems.Thm_TypeDensity_coeff_dilate
import Theorems.Thm_TypeDensity_coeff_codilate
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

theorem TypeDensity.recipSer_dilate (f : Ser) : recipSer (dilate f) = codilate (recipSer f) := by sorry
