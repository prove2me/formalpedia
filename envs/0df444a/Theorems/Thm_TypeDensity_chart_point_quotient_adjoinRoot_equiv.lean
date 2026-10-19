-- Prove2me | Theorems.Thm_TypeDensity_chart_point_quotient_adjoinRoot_equiv
-- name    : TypeDensity.chart_point_quotient_adjoinRoot_equiv
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:19.493656+00:00
-- url     : https://prove2.me/theorems/65533cf9-1209-4d32-943b-1ddc1e16b6c3
-- title:
--   For a polynomial `Φ` over `R`, the quotient of the chart `R[f/e]` by `(e, Φ(f/e))` is `(R/(e, f))[X]/(Φ̄)`.
-- statement:
--   For a polynomial `Φ` over `R`, the quotient of the chart `R[f/e]` by `(e, Φ(f/e))` is `(R/(e, f))[X]/(Φ̄)`.
-- source:
--   TypeDensity/Surfaces/ChartCompletions.lean#L290-L332

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
import Theorems.Thm_TypeDensity_exceptional_chart_is_affine_line
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

theorem TypeDensity.chart_point_quotient_adjoinRoot_equiv (R : Type) [CommRing R] (e f : R)
    (Φ : Polynomial R) :
    ∃ q : (BlowupChart R e f ⧸ Ideal.span
        {chartBase R e f e, Polynomial.eval₂ (chartBase R e f) (chartSlope R e f) Φ}) ≃+* AdjoinRoot
      (Φ.map (Ideal.Quotient.mk (Ideal.span ({e, f} : Set R)))),
      (∀ r : R, q (Ideal.Quotient.mk _ (chartBase R e f r)) = AdjoinRoot.of _
        (Ideal.Quotient.mk (Ideal.span ({e, f} : Set R)) r)) ∧ q
      (Ideal.Quotient.mk _ (chartSlope R e f)) = AdjoinRoot.root _ := by sorry
