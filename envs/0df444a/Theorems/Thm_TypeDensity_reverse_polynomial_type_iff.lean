-- Prove2me | Theorems.Thm_TypeDensity_reverse_polynomial_type_iff
-- name    : TypeDensity.reverse_polynomial_type_iff
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:53:00.655429+00:00
-- url     : https://prove2.me/theorems/c334766d-c5c6-40bb-badb-89a3f5e58819
-- title:
--   A monic `P` with `P(0) ≠ 0` has type `τ` iff its normalized reversal does.
-- statement:
--   A monic `P` with `P(0) ≠ 0` has type `τ` iff its normalized reversal does.
-- source:
--   TypeDensity/Algebra/FactorInvariant.lean#L193-L200

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_reverse_normalized_irreducible
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

theorem TypeDensity.reverse_polynomial_type_iff (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (P : Polynomial (BaseField O)) (hP : P.Monic)
    (h0 : P.coeff 0 ≠ 0) (τ : FactorType) :
    HasPolynomialTypeF O P τ ↔ HasPolynomialTypeF O (Polynomial.C (P.coeff 0)⁻¹ * P.reverse) τ := by sorry
