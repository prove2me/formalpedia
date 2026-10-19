-- Prove2me | Theorems.Thm_TypeDensity_directionPoint_properties
-- name    : TypeDensity.directionPoint_properties
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:15.593099+00:00
-- url     : https://prove2.me/theorems/7e20967b-7218-4977-87ad-b7e713aeae4c
-- title:
--   The points above affine directions of the exceptional line are maximal, contain `t`, contain the slope exactly for the direction `Z`, map to `(φ)` on the exceptional line, depend injectively on `φ`, a
-- statement:
--   The points above affine directions of the exceptional line are maximal, contain `t`, contain the slope exactly for the direction `Z`, map to `(φ)` on the exceptional line, depend injectively on `φ`, and the point above `Z` is `(t, Z)`.
-- source:
--   TypeDensity/Blowup/CurveOrders.lean#L536-L600

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

theorem TypeDensity.directionPoint_properties (R : Type) [CommRing R] [IsLocalRing R] (t x : R)
    [(Ideal.span ({t,x} : Set R)).IsMaximal] (e : (BlowupChart R t x ⧸ chartExceptional R t x) ≃+*
    Polynomial (IsLocalRing.ResidueField R)) (he : ∀ r : R, e
    (Ideal.Quotient.mk (chartExceptional R t x) (chartBase R t x r)) = Polynomial.C
    (IsLocalRing.residue R r)) (heZ : e (Ideal.Quotient.mk (chartExceptional R t x)
    (chartSlope R t x)) = Polynomial.X) :
    (∀ φ : AffineDirection (IsLocalRing.ResidueField R), (directionPoint R t x e φ).IsMaximal ∧
        chartBase R t x t ∈ directionPoint R t x e φ ∧ (chartSlope R t x ∈ directionPoint R t x e φ
        ↔ φ = zeroAffine (IsLocalRing.ResidueField R)) ∧
        ((directionPoint R t x e φ).map (Ideal.Quotient.mk (chartExceptional R t x))).map e =
        Ideal.span {φ.val}) ∧ Function.Injective (directionPoint R t x e) ∧ directionPoint R t x e
        (zeroAffine (IsLocalRing.ResidueField R)) = Ideal.span {chartBase R t x t, chartSlope R t x} := by sorry
