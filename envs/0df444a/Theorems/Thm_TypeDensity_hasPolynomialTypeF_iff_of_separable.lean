-- Prove2me | Theorems.Thm_TypeDensity_hasPolynomialTypeF_iff_of_separable
-- name    : TypeDensity.hasPolynomialTypeF_iff_of_separable
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:48.852988+00:00
-- url     : https://prove2.me/theorems/26b3178a-7d41-48ec-b4b0-86a5f6ad47a1
-- title:
--   For separable `F` the route-F and original polynomial types agree: every factor is separable, so its closure is finite by `closure_finite_of_separable`.
-- statement:
--   For separable `F` the route-F and original polynomial types agree: every factor is separable, so its closure is finite by `closure_finite_of_separable`.
-- source:
--   TypeDensity/Algebra/AlgebraType.lean#L350-L356

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Theorems.Thm_TypeDensity_closure_finite_of_separable
import Theorems.Thm_TypeDensity_HasPolynomialTypeF_to_original
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

theorem TypeDensity.hasPolynomialTypeF_iff_of_separable (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {F : (BaseField O)[X]} {σ : FactorType} (hs : F.Separable) :
    HasPolynomialTypeF O F σ ↔ HasPolynomialType O F σ := by sorry
