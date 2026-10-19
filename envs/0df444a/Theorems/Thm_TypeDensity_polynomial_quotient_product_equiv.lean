-- Prove2me | Theorems.Thm_TypeDensity_polynomial_quotient_product_equiv
-- name    : TypeDensity.polynomial_quotient_product_equiv
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:00:42.790092+00:00
-- url     : https://prove2.me/theorems/6002bfa0-a6a9-4d44-97d2-bc6e05b38aee
-- title:
--   For distinct monic irreducibles `gᵢ` over a field, `K[X]/(∏ gᵢ) ≃ ∏ K[X]/(gᵢ)` (Chinese remainder), compatibly with `mk`.
-- statement:
--   For distinct monic irreducibles `gᵢ` over a field, `K[X]/(∏ gᵢ) ≃ ∏ K[X]/(gᵢ)` (Chinese remainder), compatibly with `mk`.
-- source:
--   TypeDensity/Unramified/FactorCells.lean#L477-L498

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Theorems.Thm_TypeDensity_distinct_monic_irreducible_coprime
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
set_option autoImplicit false

open TypeDensity
open scoped ENNReal

theorem TypeDensity.polynomial_quotient_product_equiv (K : Type) [Field K] (gs : List (Polynomial K))
    (hgs : ∀ g ∈ gs, g.Monic ∧ Irreducible g) (hd : gs.Pairwise (fun g h ↦ g ≠ h)) :
    ∃ e : AdjoinRoot gs.prod ≃ₐ[K] (∀ i : Fin gs.length, AdjoinRoot (gs.get i)),
      ∀ (P : Polynomial K) (i : Fin gs.length),
        e (AdjoinRoot.mk gs.prod P) i = AdjoinRoot.mk (gs.get i) P := by sorry
