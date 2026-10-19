-- Prove2me | Theorems.Thm_TypeDensity_local_algEquiv_maximalIdeal
-- name    : TypeDensity.local_algEquiv_maximalIdeal
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:05.290988+00:00
-- url     : https://prove2.me/theorems/301c57fd-b186-43a5-89fc-da9c66a8abe2
-- title:
--   An algebra isomorphism of local rings identifies the maximal ideals (via `comap` and `map`).
-- statement:
--   An algebra isomorphism of local rings identifies the maximal ideals (via `comap` and `map`).
-- source:
--   TypeDensity/Unramified/Extension.lean#L1148-L1158

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
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
open Polynomial IsLocalRing MeasureTheory

theorem TypeDensity.local_algEquiv_maximalIdeal (O B B' : Type) [CommRing O] [CommRing B] [CommRing B']
    [IsLocalRing B] [IsLocalRing B'] [Algebra O B] [Algebra O B'] (φ : B ≃ₐ[O] B') :
    (IsLocalRing.maximalIdeal B').comap (φ : B →+* B') = IsLocalRing.maximalIdeal B ∧
      (IsLocalRing.maximalIdeal B).map (φ : B →+* B') = IsLocalRing.maximalIdeal B' := by sorry
