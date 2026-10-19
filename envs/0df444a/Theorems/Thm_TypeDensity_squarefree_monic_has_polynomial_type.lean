-- Prove2me | Theorems.Thm_TypeDensity_squarefree_monic_has_polynomial_type
-- name    : TypeDensity.squarefree_monic_has_polynomial_type
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:02.748998+00:00
-- url     : https://prove2.me/theorems/9e90700d-c707-479f-859c-79a8535044eb
-- title:
--   A squarefree monic polynomial whose irreducible factors have finite closures has a type.
-- statement:
--   A squarefree monic polynomial whose irreducible factors have finite closures has a type.
-- source:
--   TypeDensity/Algebra/AlgebraType.lean#L364-L384

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
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
open scoped Classical

theorem TypeDensity.squarefree_monic_has_polynomial_type (O : Type) [CommRing O] [IsDomain O]
    (F : Polynomial (BaseField O)) (hF : F.Monic) (hsq : Squarefree F)
    (hfin : ∀ g ∈ normalizedFactors F, Module.Finite O (integralClosure O (AdjoinRoot g))) :
    ∃ σ : FactorType, HasPolynomialTypeF O F σ := by sorry
