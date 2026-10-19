-- Prove2me | Theorems.Thm_TypeDensity_actual_cech_preserves_exceptional_lattices
-- name    : TypeDensity.actual_cech_preserves_exceptional_lattices
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:49.619605+00:00
-- url     : https://prove2.me/theorems/7350139f-f44b-4ab5-bcb2-bebe99f41ba8
-- title:
--   The twisted Čech differential maps the lattice `(t^j) × (x^j)` into `(t^j)`.
-- statement:
--   The twisted Čech differential maps the lattice `(t^j) × (x^j)` into `(t^j)`.
-- source:
--   TypeDensity/Blowup/Charts.lean#L945-L977

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Blowup_Directions
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Blowup_Charts
import Theorems.Thm_TypeDensity_blowup_chart_relation
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

theorem TypeDensity.actual_cech_preserves_exceptional_lattices (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (d j : ℕ) :
    cechInputLattice R t x j ≤ (cechOutputLattice R t x j).comap (fullCechDifferential R t x beta d) := by sorry
