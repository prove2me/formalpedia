-- Prove2me | Theorems.Thm_TypeDensity_chartSubst_surfaceRelation
-- name    : TypeDensity.chartSubst_surfaceRelation
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:02.296924+00:00
-- url     : https://prove2.me/theorems/47d40648-0d50-49f2-9d97-54c2f60f90d6
-- title:
--   The t-chart substitution at `α` of the base-changed surface relation.
-- statement:
--   The t-chart substitution at `α` sends the base change along `ρ` of the surface relation to `ρ(π) - u'·T^(a+b)·(X + α)^b`, where `u'` is the base-changed unit after the substitution.
-- source:
--   TypeDensity/Surfaces/Lengths.lean#L636-L650

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Theorems.Thm_TypeDensity_chartSubst_apply_generators
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.PicardGroup
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.chartSubst_surfaceRelation (O O' : Type) [CommRing O] [CommRing O'] (ρ : O →+* O')
    (α : O')
    (pi : O) (u : (TwoSeries O)ˣ) (a b : ℕ) :
    chartSubst O' α (MvPowerSeries.map ρ (surfaceRelation O pi u a b)) = MvPowerSeries.C (ρ pi) -
    (substUnit O' α (baseChangeUnit O ρ u) : TwoSeries O') * axisT O' ^ (a + b) *
    (axisX O' + MvPowerSeries.C α) ^ b := by sorry
