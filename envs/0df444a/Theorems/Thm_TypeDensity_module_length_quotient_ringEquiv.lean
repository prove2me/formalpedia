-- Prove2me | Theorems.Thm_TypeDensity_module_length_quotient_ringEquiv
-- name    : TypeDensity.module_length_quotient_ringEquiv
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:30:38.20013+00:00
-- url     : https://prove2.me/theorems/ba18c7c3-11c9-4678-bf0c-7954dbf08291
-- title:
--   Lengths of quotients are invariant under ring isomorphisms.
-- statement:
--   Lengths of quotients are invariant under ring isomorphisms.
-- source:
--   TypeDensity/Surfaces/Lengths.lean#L1258-L1280

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
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

theorem TypeDensity.module_length_quotient_ringEquiv (S S' : Type) [CommRing S] [CommRing S'] (e : S ≃+* S')
    (I : Ideal S) :
    Module.length S (S ⧸ I) = Module.length S' (S' ⧸ Ideal.map (e : S →+* S') I) := by sorry
