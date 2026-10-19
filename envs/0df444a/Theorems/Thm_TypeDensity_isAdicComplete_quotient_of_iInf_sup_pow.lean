-- Prove2me | Theorems.Thm_TypeDensity_isAdicComplete_quotient_of_iInf_sup_pow
-- name    : TypeDensity.isAdicComplete_quotient_of_iInf_sup_pow
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:43.465559+00:00
-- url     : https://prove2.me/theorems/fcd1aee0-7c1d-409c-beff-4f3166eabab5
-- title:
--   The quotient of an `I`-adically complete ring by an `I`-closed ideal `J` is complete for the image of `I`.
-- statement:
--   The quotient of an `I`-adically complete ring by an `I`-closed ideal `J` is complete for the image of `I`.
-- source:
--   TypeDensity/Surfaces/Lengths.lean#L1081-L1133

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

theorem TypeDensity.isAdicComplete_quotient_of_iInf_sup_pow (S : Type) [CommRing S] (I J : Ideal S)
    [IsAdicComplete I S] (hJ : (⨅ n : ℕ, J ⊔ I ^ n) = J) :
    IsAdicComplete (I.map (Ideal.Quotient.mk J)) (S ⧸ J) := by sorry
