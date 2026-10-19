-- Prove2me | Theorems.Thm_TypeDensity_isAdicComplete_of_isAdicComplete_maximalIdeal
-- name    : TypeDensity.isAdicComplete_of_isAdicComplete_maximalIdeal
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:00:51.361645+00:00
-- url     : https://prove2.me/theorems/554ee55c-3a56-436f-b553-3387d414f98f
-- title:
--   A Noetherian local ring complete for `𝔪` is complete for every proper ideal.
-- statement:
--   A Noetherian local ring complete for `𝔪` is complete for every proper ideal.
-- source:
--   TypeDensity/Surfaces/Lengths.lean#L1017-L1042

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

theorem TypeDensity.isAdicComplete_of_isAdicComplete_maximalIdeal (A : Type) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A] (J : Ideal A) (hJ : J ≠ ⊤) :
    IsAdicComplete J A := by sorry
