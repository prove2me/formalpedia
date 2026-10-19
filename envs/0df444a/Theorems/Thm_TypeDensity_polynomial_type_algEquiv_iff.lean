-- Prove2me | Theorems.Thm_TypeDensity_polynomial_type_algEquiv_iff
-- name    : TypeDensity.polynomial_type_algEquiv_iff
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:44:14.65077+00:00
-- url     : https://prove2.me/theorems/127c6bae-1a08-4006-9f46-d5947f44a50c
-- title:
--   For monic `F, F'` with `Frac O[X]/(F) ≅ Frac O[X]/(F')`, `F` has type `σ` iff `F'` does.
-- statement:
--   For monic `F, F'` with `Frac O[X]/(F) ≅ Frac O[X]/(F')`, `F` has type `σ` iff `F'` does.
-- source:
--   TypeDensity/Unramified/PolynomialTypes.lean#L116-L122

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_integral_closure_algEquiv
import Theorems.Thm_TypeDensity_factor_invariant_algEquiv
import Theorems.Thm_TypeDensity_monic_squarefree_factors_of_reduced
import Theorems.Thm_TypeDensity_pi_fields_algEquiv_index_bijection
import Theorems.Thm_TypeDensity_polynomial_quotient_product_equiv
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
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms
set_option autoImplicit false

open TypeDensity
open scoped ENNReal

theorem TypeDensity.polynomial_type_algEquiv_iff (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (F F' : Polynomial (BaseField O)) (hF : F.Monic)
    (hF' : F'.Monic) (e : AdjoinRoot F ≃ₐ[BaseField O] AdjoinRoot F') (σ : FactorType) :
    HasPolynomialTypeF O F σ ↔ HasPolynomialTypeF O F' σ := by sorry
