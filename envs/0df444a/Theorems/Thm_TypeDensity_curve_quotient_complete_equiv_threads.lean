-- Prove2me | Theorems.Thm_TypeDensity_curve_quotient_complete_equiv_threads
-- name    : TypeDensity.curve_quotient_complete_equiv_threads
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:41.34866+00:00
-- url     : https://prove2.me/theorems/d923064a-5300-486d-8e3c-03b1e056d8f2
-- title:
--   For a complete Noetherian local ring `S` and `e` in its maximal ideal, `S/(g)` is the inverse limit of the quotients `S/(g, e^j)`.
-- statement:
--   For a complete Noetherian local ring `S` and `e` in its maximal ideal, `S/(g)` is the inverse limit of the quotients `S/(g, e^j)`.
-- source:
--   TypeDensity/Blowup/CurveOrders.lean#L220-L282

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Definitions.Def_TypeDensity_Formula_FiniteFieldCounts
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Blowup_Directions
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Blowup_Charts
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_iInf_sup_pow_eq_of_isLocalRing
import Theorems.Thm_TypeDensity_isAdicComplete_of_isAdicComplete_maximalIdeal
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
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.PicardGroup
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.curve_quotient_complete_equiv_threads (S : Type) [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] [IsAdicComplete (IsLocalRing.maximalIdeal S) S] (e g : S)
    (he : e ∈ IsLocalRing.maximalIdeal S) :
    ∃ E : (S ⧸ Ideal.span {g}) ≃ {u : ∀ j : ℕ, S ⧸ Ideal.span {g, e^j} // ∀ j, levelReduction e g j
        (u (j+1)) = u j}, ∀ s : S, ∀ j : ℕ, (E (Ideal.Quotient.mk (Ideal.span {g}) s)).val j =
        Ideal.Quotient.mk (Ideal.span {g, e^j}) s := by sorry
