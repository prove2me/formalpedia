-- Prove2me | Theorems.Thm_TypeDensity_unramified_base_invariants
-- name    : TypeDensity.unramified_base_invariants
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:12.934737+00:00
-- url     : https://prove2.me/theorems/0c3e5c80-9552-46a5-be40-8c9df0c0c94d
-- title:
--   A finite free extension of DVRs of rank `δ` in which a uniformizer stays irreducible has ramification index `1` and inertia degree `δ`.
-- statement:
--   A finite free extension of DVRs of rank `δ` in which a uniformizer stays irreducible has ramification index `1` and inertia degree `δ`.
-- source:
--   TypeDensity/Unramified/FrobeniusDescent.lean#L165-L194

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_finite_flat_local_ramification_degree
import Theorems.Thm_TypeDensity_dvr_extension_maximalIdeal_map_eq_pow
import Theorems.Thm_TypeDensity_dvr_maximalIdeal_pow_injective
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

theorem TypeDensity.unramified_base_invariants (O Oδ : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CommRing Oδ] [IsDomain Oδ] [IsDiscreteValuationRing Oδ]
    [Algebra O Oδ] [Module.Finite O Oδ] [Module.Free O Oδ] (δ : ℕ)
    (hrank : Module.finrank O Oδ = δ) (pi : O) (hpi : Irreducible pi)
    (hpiδ : Irreducible (algebraMap O Oδ pi)) :
    (IsLocalRing.maximalIdeal Oδ).ramificationIdx O = 1 ∧
      (IsLocalRing.maximalIdeal Oδ).inertiaDeg O = δ := by sorry
