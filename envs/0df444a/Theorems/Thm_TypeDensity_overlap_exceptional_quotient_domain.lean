-- Prove2me | Theorems.Thm_TypeDensity_overlap_exceptional_quotient_domain
-- name    : TypeDensity.overlap_exceptional_quotient_domain
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:32:36.935981+00:00
-- url     : https://prove2.me/theorems/59fded7e-46c3-41f1-b4f1-3007f7e8216b
-- title:
--   The exceptional divisor of the overlap is integral, and an element of the opposite chart vanishing on it lies in the exceptional ideal `(x)` of that chart.
-- statement:
--   The exceptional divisor of the overlap is integral, and an element of the opposite chart vanishing on it lies in the exceptional ideal `(x)` of that chart.
-- source:
--   TypeDensity/Blowup/PointTransport.lean#L741-L825

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
import Theorems.Thm_TypeDensity_exceptional_chart_is_affine_line
import Theorems.Thm_TypeDensity_exceptional_overlap_is_laurent_line
import Theorems.Thm_TypeDensity_localization_principal_quotient_commute
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

theorem TypeDensity.overlap_exceptional_quotient_domain (R : Type) [CommRing R] (t x : R)
    [(Ideal.span ({t,x} : Set R)).IsMaximal] (_hreg : RegularParameterPair R t x)
    (beta : BlowupRestriction R t x) :
    IsDomain (BlowupOverlap R t x ⧸ Ideal.span {overlapException R t x}) ∧ ∀ b : BlowupChart R x t,
    Ideal.Quotient.mk (Ideal.span {overlapException R t x}) (beta.right b) = 0 → b ∈ Ideal.span
    {chartBase R x t x} := by sorry
