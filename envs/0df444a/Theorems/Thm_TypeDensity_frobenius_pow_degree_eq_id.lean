-- Prove2me | Theorems.Thm_TypeDensity_frobenius_pow_degree_eq_id
-- name    : TypeDensity.frobenius_pow_degree_eq_id
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:52:32.938423+00:00
-- url     : https://prove2.me/theorems/d0839e81-dd45-4cc7-884a-d1eac8069d88
-- title:
--   The `deg Φ`-th iterate of the Frobenius is the identity;
-- statement:
--   The `deg Φ`-th iterate of the Frobenius is the identity; in particular the Frobenius is bijective.
-- source:
--   TypeDensity/Unramified/FrobeniusDescent.lean#L572-L616

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_unramified_adic_complete
import Theorems.Thm_TypeDensity_simple_root_derivative_unit
import Theorems.Thm_TypeDensity_frobenius_residue_action
import Theorems.Thm_TypeDensity_residue_extension_field
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
open scoped BigOperators ENNReal

theorem TypeDensity.frobenius_pow_degree_eq_id (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) :
    frobeniusIter O Φ Φ.natDegree = AlgHom.id O (AdjoinRoot Φ) ∧
      Function.Bijective (unramifiedFrobenius O Φ) := by sorry
