-- Prove2me | Theorems.Thm_TypeDensity_polynomial_type_dvd
-- name    : TypeDensity.polynomial_type_dvd
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:00:35.579875+00:00
-- url     : https://prove2.me/theorems/4533acda-e474-4cf8-8b89-82731c41eb28
-- title:
--   A monic divisor of a polynomial with a type has a type.
-- statement:
--   A monic divisor of a polynomial with a type has a type.
-- source:
--   TypeDensity/Algebra/AlgebraType.lean#L386-L403

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Theorems.Thm_TypeDensity_squarefree_monic_has_polynomial_type
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
import Mathlib.RingTheory.Henselian
set_option autoImplicit false

open TypeDensity
open scoped TensorProduct
open Polynomial IsLocalRing
open UniqueFactorizationMonoid

theorem TypeDensity.polynomial_type_dvd (O : Type) [CommRing O] [IsDomain O]
    (F G : Polynomial (BaseField O)) (σ : FactorType)
    (hF : HasPolynomialTypeF O F σ) (hG : G.Monic) (hdvd : G ∣ F) :
    ∃ τ : FactorType, HasPolynomialTypeF O G τ := by sorry
