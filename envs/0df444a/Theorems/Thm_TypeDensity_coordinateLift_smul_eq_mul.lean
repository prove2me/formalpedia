-- Prove2me | Theorems.Thm_TypeDensity_coordinateLift_smul_eq_mul
-- name    : TypeDensity.coordinateLift_smul_eq_mul
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:12.361321+00:00
-- url     : https://prove2.me/theorems/7375cfb9-db26-4005-a358-51b3316ea47c
-- title:
--   Scaling the coordinates by `a ∈ O` multiplies their lift by the image of `a`.
-- statement:
--   Scaling the coordinates by `a ∈ O` multiplies their lift by the image of `a`.
-- source:
--   TypeDensity/Measure/AdicCylinders.lean#L101-L105

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.MvPolynomial
set_option autoImplicit false

open TypeDensity
open MeasureTheory
open scoped BigOperators ENNReal
variable {O R : Type} [CommRing O] [CommRing R] [Algebra O R]

theorem TypeDensity.coordinateLift_smul_eq_mul {n : ℕ} (b : Fin n → R) (a : O) (z : Fin n → O) :
    coordinateLift b (a • z) = algebraMap O R a * coordinateLift b z := by sorry
