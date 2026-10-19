-- Prove2me | Theorems.Thm_TypeDensity_surfaceIdeal_ne_top
-- name    : TypeDensity.surfaceIdeal_ne_top
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:01.582903+00:00
-- url     : https://prove2.me/theorems/2d355141-48c1-4225-be80-dd7a34f06dcd
-- title:
--   The surface ideal is proper when `π` is not a unit and `a > 0`.
-- statement:
--   The surface ideal is proper when `π` is not a unit and `a > 0`.
-- source:
--   TypeDensity/Surfaces/PowerSeries.lean#L993-L999

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Theorems.Thm_TypeDensity_surfaceRelation_constantCoeff
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.PicardGroup
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.surfaceIdeal_ne_top (O : Type) [CommRing O] (pi : O) (u : (TwoSeries O)ˣ) (a b : ℕ)
    (hpi : ¬ IsUnit pi) (ha : 0 < a) :
    surfaceIdeal O pi u a b ≠ ⊤ := by sorry
