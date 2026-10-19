-- Prove2me | Theorems.Thm_TypeDensity_regular_principal_generators_associated
-- name    : TypeDensity.regular_principal_generators_associated
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:41.077979+00:00
-- url     : https://prove2.me/theorems/672632d1-46db-46a4-bd59-501505f99ddf
-- title:
--   Two generators of the same principal ideal, one of them regular, differ by a unit.
-- statement:
--   Two generators of the same principal ideal, one of them regular, differ by a unit.
-- source:
--   TypeDensity/Measure/HenselProducts.lean#L1144-L1156

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

theorem TypeDensity.regular_principal_generators_associated (A : Type) [CommRing A] (f g : A)
    (hf : Function.Injective (fun x : A => x*f)) (hfg : Ideal.span {f} = Ideal.span {g}) :
    ∃ u : Aˣ, g = (u : A)*f := by sorry
