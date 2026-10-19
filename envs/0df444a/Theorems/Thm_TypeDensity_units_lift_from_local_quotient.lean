-- Prove2me | Theorems.Thm_TypeDensity_units_lift_from_local_quotient
-- name    : TypeDensity.units_lift_from_local_quotient
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:41.801423+00:00
-- url     : https://prove2.me/theorems/e43e2b95-28d7-4c58-9297-a2daf1b9b573
-- title:
--   Units of `R/I` lift to units of `R` when `I` lies in the maximal ideal of the local ring `R`.
-- statement:
--   Units of `R/I` lift to units of `R` when `I` lies in the maximal ideal of the local ring `R`.
-- source:
--   TypeDensity/Measure/PrimitiveLocus.lean#L107-L122

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
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
import Mathlib.RingTheory.Henselian
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms
set_option autoImplicit false

open TypeDensity
open MeasureTheory
open scoped BigOperators ENNReal

theorem TypeDensity.units_lift_from_local_quotient (R : Type) [CommRing R] [IsLocalRing R] (I : Ideal R)
    (hI : I ≤ IsLocalRing.maximalIdeal R) (v : (R ⧸ I)ˣ) :
    ∃ u : Rˣ, Ideal.Quotient.mk I (u : R) = (v : R ⧸ I) := by sorry
