-- Prove2me | Theorems.Thm_TypeDensity_boundary_contact_of_twisted_generator
-- name    : TypeDensity.boundary_contact_of_twisted_generator
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:44.891007+00:00
-- url     : https://prove2.me/theorems/dd804a35-a4ce-4a4a-9e34-44f558f9f82d
-- title:
--   If `f = ∑ cᵢ t^(d-i) xⁱ`, then in the chart `R[t/x]` the function `f` factors as `x^d · ∑ cᵢ (t/x)^(d-i)`, and the boundary contact of `f` with `t = 0` is `d` plus the contact of the strict transform
-- statement:
--   If `f = ∑ cᵢ t^(d-i) xⁱ`, then in the chart `R[t/x]` the function `f` factors as `x^d · ∑ cᵢ (t/x)^(d-i)`, and the boundary contact of `f` with `t = 0` is `d` plus the contact of the strict transform with the slope divisor.
-- source:
--   TypeDensity/Blowup/DivisorPoints.lean#L92-L149

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
import Definitions.Def_TypeDensity_Surfaces_TruncatedSeries
import Definitions.Def_TypeDensity_Surfaces_ConcreteAtlas
import Definitions.Def_TypeDensity_Blowup_DivisorPoints
import Theorems.Thm_TypeDensity_blowup_chart_relation
import Theorems.Thm_TypeDensity_boundary_chart_quotient_equiv
import Theorems.Thm_TypeDensity_quotient_ring_length_intrinsic
import Theorems.Thm_TypeDensity_length_quotient_sup_mul_eq_add
import Theorems.Thm_TypeDensity_length_quotient_sup_pow_eq_mul
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
import Mathlib.Algebra.Group.NatPowAssoc
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.boundary_contact_of_twisted_generator (R : Type) [CommRing R] (t x : R)
    [(Ideal.span ({t,x} : Set R)).IsMaximal] (hreg : RegularParameterPair R t x) (d : ℕ) (f : R)
    (c : Fin (d + 1) → R) (hc : f = ∑ i : Fin (d + 1), c i * t ^ (d - i.val) * x ^ i.val) :
    algebraMap R (BlowupChart R x t) f = (chartBase R x t x)^d *
        ∑ i : Fin (d+1), algebraMap R (BlowupChart R x t) (c i) * (chartSlope R x t)^(d - i.val) ∧
      Module.length R (R ⧸ (Ideal.span {f} ⊔ Ideal.span {t})) = (d : ℕ∞) +
        Module.length (BlowupChart R x t) (BlowupChart R x t ⧸
          (Ideal.span {∑ i : Fin (d+1), algebraMap R (BlowupChart R x t) (c i) *
            (chartSlope R x t)^(d - i.val)} ⊔ Ideal.span {chartSlope R x t})) := by sorry
