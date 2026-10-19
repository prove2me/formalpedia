-- Prove2me | Theorems.Thm_TypeDensity_polynomial_type_map_unramified
-- name    : TypeDensity.polynomial_type_map_unramified
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:25:26.444069+00:00
-- url     : https://prove2.me/theorems/e1ec44fb-dbea-489c-bb6b-63d096fa54d4
-- title:
--   A polynomial with a type over `O` has a type over the unramified extension `Oδ`.
-- statement:
--   A polynomial with a type over `O` has a type over the unramified extension `Oδ`.
-- source:
--   TypeDensity/Unramified/DescentTypes.lean#L282-L307

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_squarefree_map_of_isSeparable
import Theorems.Thm_TypeDensity_closure_finite_ascent_root
import Theorems.Thm_TypeDensity_squarefree_monic_has_polynomial_type
import Theorems.Thm_TypeDensity_unramified_fraction_isSeparable
import Theorems.Thm_TypeDensity_distinct_monic_irreducible_coprime
import Theorems.Thm_TypeDensity_unramified_free_module
import Theorems.Thm_TypeDensity_polynomial_type_mul_coprime
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
variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
  (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) [IsDomain (AdjoinRoot Φ)]
  (ι : BaseField O →+* BaseField (AdjoinRoot Φ))
  (hι : ∀ c : O, ι (algebraMap O (BaseField O) c) =
    algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ)) (algebraMap O (AdjoinRoot Φ) c))
include hΦ hι

theorem TypeDensity.polynomial_type_map_unramified (F : Polynomial (BaseField O)) (σ : FactorType)
    (hF : HasPolynomialTypeF O F σ) :
    ∃ τ' : FactorType, HasPolynomialTypeF (AdjoinRoot Φ) (F.map ι) τ' := by sorry
