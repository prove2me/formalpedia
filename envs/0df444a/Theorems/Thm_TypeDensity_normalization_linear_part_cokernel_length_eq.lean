-- Prove2me | Theorems.Thm_TypeDensity_normalization_linear_part_cokernel_length_eq
-- name    : TypeDensity.normalization_linear_part_cokernel_length_eq
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:10.042157+00:00
-- url     : https://prove2.me/theorems/daa49af7-d40a-4833-b8cb-b9fa54a5b148
-- title:
--   The cokernel of the linear part of the normalization map has the same `O`-length as the cokernel of the quotient map `phi`, and it is injective whenever `phi` is.
-- statement:
--   The cokernel of the linear part of the normalization map has the same `O`-length as the cokernel of the quotient map `phi`, and it is injective whenever `phi` is.
-- source:
--   TypeDensity/Blowup/PointTransport.lean#L476-L512

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
import Theorems.Thm_TypeDensity_division_equiv_child_coordinates
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

theorem TypeDensity.normalization_linear_part_cokernel_length_eq (O R C : Type) [CommRing O] [CommRing R]
    [CommRing C] [Algebra O R] [Algebra O C] (alpha : R →ₐ[O] C) (f : R) (g e c : C) (d : ℕ)
    (_hf : alpha f = e ^ d * g) (n : ℕ) (pi : O) (s : ℕ)
    (_hpi : (algebraMap O C pi) ^ s = e ^ d * c)
    (b : Fin n → R) (bc : Fin n → C) (E : C ≃ₗ[O] ((Fin n → O) × C))
    (hE : ∀ w, E.symm w = divisionMap g bc w)
    (phi : (R ⧸ Ideal.span {f}) →ₗ[O] (C ⧸ Ideal.span {g}))
    (hphi : ∀ h : R, phi (Ideal.Quotient.mk (Ideal.span {f}) h) =
      Ideal.Quotient.mk (Ideal.span {g}) (c * alpha h))
    (EB : (R ⧸ Ideal.span {f}) ≃ₗ[O] (Fin n → O))
    (hEB : ∀ z : Fin n → O, EB.symm z = Ideal.Quotient.mk (Ideal.span {f}) (coordinateLift b z)) :
    Module.length O ((Fin n → O) ⧸ LinearMap.range
      (normalizationLinearPart E (pulledVariation alpha c b))) = Module.length O
    ((C ⧸ Ideal.span {g}) ⧸ LinearMap.range phi) ∧
    (Function.Injective phi → Function.Injective
      (normalizationLinearPart E (pulledVariation alpha c b))) := by sorry
