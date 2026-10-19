-- Prove2me | Theorems.Thm_TypeDensity_glued_level_one_normalization
-- name    : TypeDensity.glued_level_one_normalization
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:36.597983+00:00
-- url     : https://prove2.me/theorems/652b2d98-d191-44d6-b9c2-f314e94358f6
-- title:
--   Normalization of glued generators at exceptional level one: if the images of the chart elements `gA` and `gB` generate the same principal ideal of the exceptional divisor of the overlap, `gA` reduces
-- statement:
--   Normalization of glued generators at exceptional level one: if the images of the chart elements `gA` and `gB` generate the same principal ideal of the exceptional divisor of the overlap, `gA` reduces to a polynomial of trailing degree `r` and `gB` to one of degree `n` with `r + n = d`, then `gA ≡ u · z^d · gB` modulo the exceptional divisor for some unit `u` of `R`.
-- source:
--   TypeDensity/Blowup/ExceptionalLayers.lean#L157-L275

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
import Theorems.Thm_TypeDensity_laurent_isUnit_iff_monomial
import Theorems.Thm_TypeDensity_regular_principal_generators_associated
import Theorems.Thm_TypeDensity_units_lift_from_local_quotient
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
open LaurentPolynomial

theorem TypeDensity.glued_level_one_normalization (R : Type) [CommRing R] (t x : R)
    [(Ideal.span ({t,x} : Set R)).IsMaximal] [IsLocalRing R] (_hreg : RegularParameterPair R t x)
    (beta : BlowupRestriction R t x) (d : ℕ) (gA : BlowupChart R t x) (gB : BlowupChart R x t)
    (hoverlap : Ideal.span {Ideal.Quotient.mk (Ideal.span {overlapException R t x})
      ((algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) gA)} =
      Ideal.span {Ideal.Quotient.mk (Ideal.span {overlapException R t x}) (beta.right gB)})
    (hregB : Function.Injective (fun c : BlowupOverlap R t x ⧸
      (Ideal.span {overlapException R t x}) => Ideal.Quotient.mk
      (Ideal.span {overlapException R t x}) (beta.right gB) * c)) (m n : ℕ) (cA : Fin (m+1) → R)
    (cB : Fin (n+1) → R) (hgA : gA - ∑ i : Fin (m+1),
      algebraMap R (BlowupChart R t x) (cA i) * (chartSlope R t x)^i.val ∈ chartExceptional R t x)
    (hgB : gB - ∑ i : Fin (n+1), algebraMap R (BlowupChart R x t) (cB i) * (chartSlope R x t)^i.val
      ∈ chartExceptional R x t) (r : ℕ) (hlow : ∀ i : Fin (m+1), i.val < r →
      cA i ∈ Ideal.span {t,x}) (hr : ∀ i : Fin (m+1), i.val = r → cA i ∉ Ideal.span {t,x})
    (hrm : r ≤ m) (htop : cB (Fin.last n) ∉ Ideal.span {t,x}) (hdeg : r + n = d) :
    ∃ u : Rˣ, (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) gA - algebraMap R
    (BlowupOverlap R t x) (u : R) * ((overlapSlope R t x)^d * beta.right gB) ∈
    (Ideal.span {overlapException R t x}) := by sorry
