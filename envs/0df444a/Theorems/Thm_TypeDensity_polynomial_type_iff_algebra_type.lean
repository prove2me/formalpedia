-- Prove2me | Theorems.Thm_TypeDensity_polynomial_type_iff_algebra_type
-- name    : TypeDensity.polynomial_type_iff_algebra_type
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:44:07.644448+00:00
-- url     : https://prove2.me/theorems/869ad725-0d0c-4489-b06d-223bdb21bcdb
-- title:
--   For monic `F ∈ O[X]`, the image of `F` in `K[X]` has polynomial type `σ` iff `O[X]/(F)` has algebra type `σ`.
-- statement:
--   For monic `F ∈ O[X]`, the image of `F` in `K[X]` has polynomial type `σ` iff `O[X]/(F)` has algebra type `σ`.
-- source:
--   TypeDensity/Algebra/FactorInvariant.lean#L273-L322

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_adjoinRoot_base_change
import Theorems.Thm_TypeDensity_squarefree_of_isReduced_adjoinRoot
import Theorems.Thm_TypeDensity_squarefree_monic_has_polynomial_type
import Theorems.Thm_TypeDensity_integral_closure_algEquiv
import Theorems.Thm_TypeDensity_pi_field_matching
import Theorems.Thm_TypeDensity_algebra_type_unique
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
open Polynomial

theorem TypeDensity.polynomial_type_iff_algebra_type (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (F : Polynomial O) (hF : F.Monic) (σ : FactorType) :
    HasPolynomialTypeF O (F.map (algebraMap O (BaseField O))) σ ↔
      HasAlgebraType O (AdjoinRoot F) σ := by sorry
