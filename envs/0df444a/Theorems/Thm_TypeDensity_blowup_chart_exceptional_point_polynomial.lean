-- Prove2me | Theorems.Thm_TypeDensity_blowup_chart_exceptional_point_polynomial
-- name    : TypeDensity.blowup_chart_exceptional_point_polynomial
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:30:26.369947+00:00
-- url     : https://prove2.me/theorems/c8afb110-ee0e-4b23-8d51-a19325a01b21
-- title:
--   Given an identification `e` of the exceptional fibre of the chart with `(R/(t,x))[Z]`, a maximal ideal `P` containing `t` corresponds to a monic irreducible `φ`: `P` maps onto `(φ)`, contains the slop
-- statement:
--   Given an identification `e` of the exceptional fibre of the chart with `(R/(t,x))[Z]`, a maximal ideal `P` containing `t` corresponds to a monic irreducible `φ`: `P` maps onto `(φ)`, contains the slope iff `φ = Z`, and has `R`-length `deg φ`.
-- source:
--   TypeDensity/Blowup/ExceptionalLayers.lean#L366-L434

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
open scoped BigOperators ENNReal

theorem TypeDensity.blowup_chart_exceptional_point_polynomial (R : Type) [CommRing R] (t x : R)
    [(Ideal.span ({t,x} : Set R)).IsMaximal]
    (e : (BlowupChart R t x ⧸ chartExceptional R t x) ≃+* Polynomial
      (R ⧸ Ideal.span ({t,x} : Set R))) (he : ∀ r : R,
      e (Ideal.Quotient.mk (chartExceptional R t x) (chartBase R t x r)) =
      Polynomial.C (Ideal.Quotient.mk (Ideal.span ({t,x} : Set R)) r))
    (heZ : e (Ideal.Quotient.mk (chartExceptional R t x) (chartSlope R t x)) = Polynomial.X)
    (P : Ideal (BlowupChart R t x)) [P.IsMaximal] (hP : chartBase R t x t ∈ P) :
    ∃ φ : Polynomial (R ⧸ Ideal.span ({t,x} : Set R)), φ.Monic ∧ Irreducible φ ∧
    (P.map (Ideal.Quotient.mk (chartExceptional R t x))).map e = Ideal.span {φ} ∧
    (chartSlope R t x ∈ P ↔ φ = Polynomial.X) ∧ Module.length R (BlowupChart R t x ⧸ P) =
    (φ.natDegree : ℕ∞) := by sorry
