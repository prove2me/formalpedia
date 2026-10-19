-- Prove2me | Theorems.Thm_TypeDensity_actual_cech_differentials_commute_with_reduction
-- name    : TypeDensity.actual_cech_differentials_commute_with_reduction
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:30:33.119149+00:00
-- url     : https://prove2.me/theorems/9f665660-7930-4e83-b5ba-9304e7729bcf
-- title:
--   The level Čech differentials commute with the reduction maps.
-- statement:
--   The level Čech differentials commute with the reduction maps.
-- source:
--   TypeDensity/Blowup/Charts.lean#L979-L987

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Blowup_Directions
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Blowup_Charts
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.PicardGroup
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.actual_cech_differentials_commute_with_reduction (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (d j : ℕ) (hnext : cechInputLattice R t x (j + 1) ≤
    (cechOutputLattice R t x (j + 1)).comap (fullCechDifferential R t x beta d))
    (hnow : cechInputLattice R t x j ≤ (cechOutputLattice R t x j).comap
    (fullCechDifferential R t x beta d)) :
    (cechOutputReduction R t x j).comp (finiteCechDifferential R t x beta d (j+1) hnext) =
        (finiteCechDifferential R t x beta d j hnow).comp (cechInputReduction R t x j) := by sorry
