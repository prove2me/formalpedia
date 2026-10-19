-- Prove2me | Theorems.Thm_TypeDensity_division_equiv_child_coordinates
-- name    : TypeDensity.division_equiv_child_coordinates
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:53.657856+00:00
-- url     : https://prove2.me/theorems/60580efc-b904-49a7-9111-ea955b77d103
-- title:
--   A division-chart decomposition `C ≃ O^n × C` with second factor multiplied by `g` induces `C/(g) ≃ O^n`.
-- statement:
--   A division-chart decomposition `C ≃ O^n × C` with second factor multiplied by `g` induces `C/(g) ≃ O^n`.
-- source:
--   TypeDensity/Blowup/CurveOrders.lean#L1000-L1041

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

theorem TypeDensity.division_equiv_child_coordinates (O C : Type) [CommRing O] [CommRing C] [Algebra O C]
    (n : ℕ) (g : C) (bc : Fin n → C) (E : C ≃ₗ[O] ((Fin n → O) × C))
    (hE : ∀ w, E.symm w = divisionMap g bc w) :
    ∃ EC : (C ⧸ Ideal.span {g}) ≃ₗ[O] (Fin n → O), ∀ w : C, EC
        (Ideal.Quotient.mk (Ideal.span {g}) w) = (E w).1 := by sorry
