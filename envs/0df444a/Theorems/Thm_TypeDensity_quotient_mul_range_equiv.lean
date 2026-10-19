-- Prove2me | Theorems.Thm_TypeDensity_quotient_mul_range_equiv
-- name    : TypeDensity.quotient_mul_range_equiv
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:53.439705+00:00
-- url     : https://prove2.me/theorems/f170c234-9ba0-4f50-bbf2-859b34d6acda
-- title:
--   `(C/I) / e(C/I) ≃ C/(I + (e))` as `O`-modules, compatibly with the quotient maps.
-- statement:
--   `(C/I) / e(C/I) ≃ C/(I + (e))` as `O`-modules, compatibly with the quotient maps.
-- source:
--   TypeDensity/Measure/HenselProducts.lean#L1103-L1142

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

theorem TypeDensity.quotient_mul_range_equiv (O C : Type) [CommRing O] [CommRing C] [Algebra O C] (I : Ideal C)
    (e : C) :
    ∃ φ : ((C ⧸ I) ⧸ LinearMap.range (LinearMap.mulLeft O (Ideal.Quotient.mk I e))) ≃ₗ[O]
      (C ⧸ (I ⊔ Ideal.span {e})),
      ∀ x : C, φ (Submodule.Quotient.mk (Ideal.Quotient.mk I x)) =
      Ideal.Quotient.mk (I ⊔ Ideal.span {e}) x := by sorry
