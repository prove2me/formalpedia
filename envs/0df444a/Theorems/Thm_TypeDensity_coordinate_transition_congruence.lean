-- Prove2me | Theorems.Thm_TypeDensity_coordinate_transition_congruence
-- name    : TypeDensity.coordinate_transition_congruence
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:21.074594+00:00
-- url     : https://prove2.me/theorems/45ac2f80-dc47-4f97-ad84-0bdf4413f063
-- title:
--   The transition between the coordinates of two normalizations preserves congruence modulo `(π)^j`.
-- statement:
--   The transition between the coordinates of two normalizations preserves congruence modulo `(π)^j`.
-- source:
--   TypeDensity/Measure/Normalizer.lean#L76-L101

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Definitions.Def_TypeDensity_Formula_FiniteFieldCounts
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Blowup_Directions
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Blowup_Charts
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Definitions.Def_TypeDensity_Surfaces_TruncatedSeries
import Theorems.Thm_TypeDensity_coordinate_remainder_raises_order
import Theorems.Thm_TypeDensity_adic_perturb_congruence_iff
import Theorems.Thm_TypeDensity_adic_perturb_bijective
import Theorems.Thm_TypeDensity_linear_map_preserves_adic_congruence
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
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.PicardGroup
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.coordinate_transition_congruence (O R : Type) [CommRing O] [CommRing R] [Algebra O R]
    (n : ℕ) (pi : O) (b : Fin n → R)
    [IsAdicComplete (Ideal.span {pi}) ((Fin n → O) × R)] (c : Fin n → R)
    (F : R ≃ₗ[O] ((Fin n → O) × R)) (h0 : R) (j : ℕ) (z w : Fin n → O)
    (hzw : adicCongr (Ideal.span {pi}) j z w) :
    adicCongr (Ideal.span {pi}) j (idealTransition pi b c F h0 z)
      (idealTransition pi b c F h0 w) := by sorry
