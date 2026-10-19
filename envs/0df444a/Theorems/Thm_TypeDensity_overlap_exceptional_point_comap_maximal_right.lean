-- Prove2me | Theorems.Thm_TypeDensity_overlap_exceptional_point_comap_maximal_right
-- name    : TypeDensity.overlap_exceptional_point_comap_maximal_right
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:32:24.435287+00:00
-- url     : https://prove2.me/theorems/9eb5d366-377e-4f77-9a74-ce66df4151a4
-- title:
--   A maximal ideal of the overlap containing the exceptional parameter contracts, along the gluing map, to a maximal ideal of the opposite chart that contains `x` but not its slope.
-- statement:
--   A maximal ideal of the overlap containing the exceptional parameter contracts, along the gluing map, to a maximal ideal of the opposite chart that contains `x` but not its slope.
-- source:
--   TypeDensity/Blowup/PointTransport.lean#L679-L704

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
import Theorems.Thm_TypeDensity_blowup_chart_relation
import Theorems.Thm_TypeDensity_blowup_overlap_isLocalization_right
import Theorems.Thm_TypeDensity_comap_isMaximal_of_exceptional
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
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.overlap_exceptional_point_comap_maximal_right (R : Type) [CommRing R] (t x : R)
    [(Ideal.span ({t,x} : Set R)).IsMaximal] (beta : BlowupRestriction R t x)
    (Q : Ideal (BlowupOverlap R t x)) [Q.IsMaximal]
    (hQ : (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (chartBase R t x t) ∈ Q) :
    (Q.comap beta.right.toRingHom).IsMaximal ∧ chartSlope R x t ∉ Q.comap beta.right.toRingHom ∧
    chartBase R x t x ∈ Q.comap beta.right.toRingHom := by sorry
