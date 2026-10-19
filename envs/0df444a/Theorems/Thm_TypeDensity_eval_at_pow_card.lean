-- Prove2me | Theorems.Thm_TypeDensity_eval_at_pow_card
-- name    : TypeDensity.eval_at_pow_card
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:09.604301+00:00
-- url     : https://prove2.me/theorems/1b538b06-c87d-4673-8061-72397c20d4c5
-- title:
--   Over a finite field `k` with `q` elements, `P(y^q) = P(y)^q` for `P ∈ k[X]`.
-- statement:
--   Over a finite field `k` with `q` elements, `P(y^q) = P(y)^q` for `P ∈ k[X]`.
-- source:
--   TypeDensity/Unramified/Extension.lean#L494-L501

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

theorem TypeDensity.eval_at_pow_card (k K : Type) [Field k] [Finite k] [CommRing K] (ρ : k →+* K)
    (P : Polynomial k) (y : K) :
    P.eval₂ ρ (y ^ Nat.card k) = (P.eval₂ ρ y) ^ Nat.card k := by sorry
