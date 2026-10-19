-- Prove2me | Theorems.Thm_TypeDensity_chart_nonrational_point_span_eq_comap
-- name    : TypeDensity.chart_nonrational_point_span_eq_comap
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:32:03.846119+00:00
-- url     : https://prove2.me/theorems/bd1d16b3-3e40-49cd-afe8-48ff0399c624
-- title:
--   If `Φ̄` is irreducible over the field `R/(e, f)`, then `(e, Φ(f/e))` is a maximal ideal of the chart, equal to the preimage of the maximal ideal under any local map `Λ` killing it.
-- statement:
--   If `Φ̄` is irreducible over the field `R/(e, f)`, then `(e, Φ(f/e))` is a maximal ideal of the chart, equal to the preimage of the maximal ideal under any local map `Λ` killing it.
-- source:
--   TypeDensity/Surfaces/ChartCompletions.lean#L334-L360

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
import Theorems.Thm_TypeDensity_chart_point_quotient_adjoinRoot_equiv
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

theorem TypeDensity.chart_nonrational_point_span_eq_comap (R : Type) [CommRing R] (e f : R)
    [(Ideal.span ({e, f} : Set R)).IsMaximal] (Φ : Polynomial R)
    (hΦ : Irreducible (Φ.map (Ideal.Quotient.mk (Ideal.span ({e, f} : Set R))))) (S : Type)
    [CommRing S] [IsLocalRing S] (Λ : BlowupChart R e f →+* S)
    (he : Λ (chartBase R e f e) ∈ IsLocalRing.maximalIdeal S)
    (hΦZ : Λ (Polynomial.eval₂ (chartBase R e f) (chartSlope R e f) Φ)
      ∈ IsLocalRing.maximalIdeal S) :
    (Ideal.span
        {chartBase R e f e, Polynomial.eval₂ (chartBase R e f) (chartSlope R e f) Φ}).IsMaximal ∧
      Ideal.span {chartBase R e f e, Polynomial.eval₂ (chartBase R e f) (chartSlope R e f) Φ} =
      (IsLocalRing.maximalIdeal S).comap Λ := by sorry
