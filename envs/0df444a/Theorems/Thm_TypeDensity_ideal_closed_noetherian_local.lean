-- Prove2me | Theorems.Thm_TypeDensity_ideal_closed_noetherian_local
-- name    : TypeDensity.ideal_closed_noetherian_local
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:29.840195+00:00
-- url     : https://prove2.me/theorems/bfa26cf4-082c-4331-999c-ea2bc889b2bc
-- title:
--   Every ideal of a Noetherian local ring is closed in the `𝔪`-adic topology.
-- statement:
--   Every ideal of a Noetherian local ring is closed in the `𝔪`-adic topology.
-- source:
--   TypeDensity/Surfaces/Lengths.lean#L1011-L1015

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Theorems.Thm_TypeDensity_iInf_sup_pow_eq_of_isLocalRing
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

theorem TypeDensity.ideal_closed_noetherian_local (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (I : Ideal A) :
    ⨅ n : ℕ, (I ⊔ (IsLocalRing.maximalIdeal A)^n) = I := by sorry
