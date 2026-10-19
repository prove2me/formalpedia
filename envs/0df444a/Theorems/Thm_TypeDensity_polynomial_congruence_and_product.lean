-- Prove2me | Theorems.Thm_TypeDensity_polynomial_congruence_and_product
-- name    : TypeDensity.polynomial_congruence_and_product
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:01.433981+00:00
-- url     : https://prove2.me/theorems/b374e5cb-8f2e-477c-a5b5-9cc9834044d5
-- title:
--   Two polynomials agree modulo `I` iff their coefficients do, and coefficientwise congruence mod `I` is preserved by finite products.
-- statement:
--   Two polynomials agree modulo `I` iff their coefficients do, and coefficientwise congruence mod `I` is preserved by finite products.
-- source:
--   TypeDensity/Unramified/FactorCells.lean#L462-L475

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
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

theorem TypeDensity.polynomial_congruence_and_product (O : Type) [CommRing O] (I : Ideal O) :
    (∀ P Q : Polynomial O, P.map (Ideal.Quotient.mk I) = Q.map (Ideal.Quotient.mk I) ↔
        ∀ j, P.coeff j - Q.coeff j ∈ I) ∧
      (∀ (ι : Type) [Fintype ι] (F F' : ι → Polynomial O),
        (∀ i j, (F i).coeff j - (F' i).coeff j ∈ I) →
          ∀ j, (∏ i, F i).coeff j - (∏ i, F' i).coeff j ∈ I) := by sorry
