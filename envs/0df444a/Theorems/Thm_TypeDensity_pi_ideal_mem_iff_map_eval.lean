-- Prove2me | Theorems.Thm_TypeDensity_pi_ideal_mem_iff_map_eval
-- name    : TypeDensity.pi_ideal_mem_iff_map_eval
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:53.083861+00:00
-- url     : https://prove2.me/theorems/9a230d77-efa3-44b9-8751-c0dcf2319c7d
-- title:
--   An ideal of a finite product of rings is determined by its images in the factors.
-- statement:
--   An ideal of a finite product of rings is determined by its images in the factors.
-- source:
--   TypeDensity/Measure/HenselProducts.lean#L792-L815

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
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
set_option autoImplicit false

open TypeDensity
open MeasureTheory
open scoped BigOperators ENNReal

theorem TypeDensity.pi_ideal_mem_iff_map_eval (ι : Type) [Finite ι] (R : ι → Type) [∀ j, CommRing (R j)]
    (I : Ideal (∀ j, R j)) :
    (∀ x : ∀ j, R j, x ∈ I ↔ ∀ j, x j ∈ I.map (Pi.evalRingHom R j)) ∧ ∀ J : Ideal (∀ j, R j),
      (∀ j, I.map (Pi.evalRingHom R j) = J.map (Pi.evalRingHom R j)) → I = J := by sorry
