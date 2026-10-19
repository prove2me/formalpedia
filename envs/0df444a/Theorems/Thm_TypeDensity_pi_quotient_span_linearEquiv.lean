-- Prove2me | Theorems.Thm_TypeDensity_pi_quotient_span_linearEquiv
-- name    : TypeDensity.pi_quotient_span_linearEquiv
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:53.301982+00:00
-- url     : https://prove2.me/theorems/ad101c29-d142-462d-b63a-4596bb4a8861
-- title:
--   Quotients of a finite product of `O`-algebras by `(g)` and by `(g, e)` are the products of the componentwise quotients.
-- statement:
--   Quotients of a finite product of `O`-algebras by `(g)` and by `(g, e)` are the products of the componentwise quotients.
-- source:
--   TypeDensity/Measure/HenselProducts.lean#L836-L866

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

theorem TypeDensity.pi_quotient_span_linearEquiv (O : Type) [CommRing O] (ι : Type) (C : ι → Type)
    [∀ j, CommRing (C j)] [∀ j, Algebra O (C j)] (g e : ∀ j, C j) :
    (∃ ψ : ((∀ j, C j) ⧸ Ideal.span {g}) ≃ₗ[O] (∀ j, C j ⧸ Ideal.span {g j}),
      ∀ x : ∀ j, C j, ψ (Ideal.Quotient.mk (Ideal.span {g}) x) =
        fun j => Ideal.Quotient.mk (Ideal.span {g j}) (x j)) ∧
      ∃ ψ' : ((∀ j, C j) ⧸ (Ideal.span {g} ⊔ Ideal.span {e})) ≃ₗ[O]
        (∀ j, C j ⧸ (Ideal.span {g j} ⊔ Ideal.span {e j})),
      ∀ x : ∀ j, C j, ψ' (Ideal.Quotient.mk (Ideal.span {g} ⊔ Ideal.span {e}) x) =
      fun j => Ideal.Quotient.mk (Ideal.span {g j} ⊔ Ideal.span {e j}) (x j) := by sorry
