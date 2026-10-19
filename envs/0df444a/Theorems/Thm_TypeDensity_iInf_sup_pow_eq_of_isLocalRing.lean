-- Prove2me | Theorems.Thm_TypeDensity_iInf_sup_pow_eq_of_isLocalRing
-- name    : TypeDensity.iInf_sup_pow_eq_of_isLocalRing
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:44.966557+00:00
-- url     : https://prove2.me/theorems/b871e462-e550-4bf7-b847-a9564219d95a
-- title:
--   Krull intersection: in a Noetherian local ring, `⋂ₙ (J + Iⁿ) = J` for every proper `I`.
-- statement:
--   Krull intersection: in a Noetherian local ring, `⋂ₙ (J + Iⁿ) = J` for every proper `I`.
-- source:
--   TypeDensity/Surfaces/Lengths.lean#L991-L1009

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

theorem TypeDensity.iInf_sup_pow_eq_of_isLocalRing (S : Type) [CommRing S] [IsNoetherianRing S] [IsLocalRing S]
    (I J : Ideal S) (hI : I ≠ ⊤) :
    (⨅ n : ℕ, J ⊔ I ^ n) = J := by sorry
