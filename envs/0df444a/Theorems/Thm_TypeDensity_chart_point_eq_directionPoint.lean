-- Prove2me | Theorems.Thm_TypeDensity_chart_point_eq_directionPoint
-- name    : TypeDensity.chart_point_eq_directionPoint
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:40.631366+00:00
-- url     : https://prove2.me/theorems/0f2050e2-f605-47fb-a5df-e11073cbb3b2
-- title:
--   Every maximal ideal of the chart containing `t` is the direction point of an affine direction `φ` over the residue field;
-- statement:
--   Every maximal ideal of the chart containing `t` is the direction point of an affine direction `φ` over the residue field; it maps onto `(φ)` in the exceptional fibre and contains the slope iff `φ` is the zero direction.
-- source:
--   TypeDensity/Blowup/ExceptionalLayers.lean#L436-L501

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
import Theorems.Thm_TypeDensity_blowup_chart_exceptional_point_polynomial
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

theorem TypeDensity.chart_point_eq_directionPoint (R : Type) [CommRing R] [IsLocalRing R] (t x : R)
    [(Ideal.span ({t,x} : Set R)).IsMaximal]
    (e : (BlowupChart R t x ⧸ chartExceptional R t x) ≃+* Polynomial (IsLocalRing.ResidueField R))
    (he : ∀ r : R, e (Ideal.Quotient.mk (chartExceptional R t x) (chartBase R t x r)) =
      Polynomial.C (IsLocalRing.residue R r))
    (heZ : e (Ideal.Quotient.mk (chartExceptional R t x) (chartSlope R t x)) = Polynomial.X)
    (P : Ideal (BlowupChart R t x)) [P.IsMaximal] (hP : chartBase R t x t ∈ P) :
    ∃ φ : AffineDirection (IsLocalRing.ResidueField R), P = directionPoint R t x e φ ∧
    (P.map (Ideal.Quotient.mk (chartExceptional R t x))).map e = Ideal.span {φ.val} ∧
    (chartSlope R t x ∈ P ↔ φ = zeroAffine (IsLocalRing.ResidueField R)) := by sorry
