-- Prove2me | Theorems.Thm_TypeDensity_crossing_residue_ideal_count
-- name    : TypeDensity.crossing_residue_ideal_count
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:00:21.822216+00:00
-- url     : https://prove2.me/theorems/a30c0f23-21bb-4525-8315-f2dbe806f920
-- title:
--   The number of crossing residue ideals of `k⟦T, X⟧ ⧸ (T^a X^b)` with contacts `c` with `T` and `h` with `X` is `(q - 1) q^(ac + bh - c - h)`, where `q = #k`.
-- statement:
--   The number of crossing residue ideals of `k⟦T, X⟧ ⧸ (T^a X^b)` with contacts `c` with `T` and `h` with `X` is `(q - 1) q^(ac + bh - c - h)`, where `q = #k`.
-- source:
--   TypeDensity/Measure/Normalizer.lean#L181-L271

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
import Theorems.Thm_TypeDensity_finite_length_module_card
import Theorems.Thm_TypeDensity_length_double_quotient_eq
import Theorems.Thm_TypeDensity_axisQuotientLength_eq_iff
import Theorems.Thm_TypeDensity_contact_fiberT_eq_axisQuotientLength
import Theorems.Thm_TypeDensity_contact_fiberX_eq_axisQuotientLength
import Theorems.Thm_TypeDensity_card_truncIndex_axis_segment
import Theorems.Thm_TypeDensity_truncCoeffs_apply
import Theorems.Thm_TypeDensity_principal_residue_ideal_count
import Theorems.Thm_TypeDensity_crossing_special_fiber_length
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

theorem TypeDensity.crossing_residue_ideal_count (k : Type) [Field k] [Finite k] (a b c h : ℕ) (ha : 0 < a)
    (hb : 0 < b) (hc : 0 < c) (hh : 0 < h) :
    Nat.card (crossingResidueIdeals k a b c h) = (Nat.card k-1)*(Nat.card k)^(a*c+b*h-c-h) := by sorry
