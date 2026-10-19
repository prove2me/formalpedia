-- Prove2me | Theorems.Thm_TypeDensity_chart_layer_polynomial_coordinates
-- name    : TypeDensity.chart_layer_polynomial_coordinates
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:39.350396+00:00
-- url     : https://prove2.me/theorems/88343454-3fc7-4300-96ac-fc7b1ae019cb
-- title:
--   Each exceptional layer of the chart is `R`-linearly isomorphic to `(R/(t,x))[Z]`, the monomial `r Z^i` corresponding to the layer class of `r · z^i`.
-- statement:
--   Each exceptional layer of the chart is `R`-linearly isomorphic to `(R/(t,x))[Z]`, the monomial `r Z^i` corresponding to the layer class of `r · z^i`.
-- source:
--   TypeDensity/Blowup/ExceptionalLayers.lean#L752-L787

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
import Theorems.Thm_TypeDensity_blowup_exceptional_parameter_regular
import Theorems.Thm_TypeDensity_exceptional_chart_is_affine_line
import Theorems.Thm_TypeDensity_principal_layer_quotient_equiv
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

theorem TypeDensity.chart_layer_polynomial_coordinates (R : Type) [CommRing R] (t x : R)
    (hreg : RegularParameterPair R t x) (j : ℕ) :
    ∃ L : Polynomial (R ⧸ Ideal.span {t,x}) ≃ₗ[R] PrincipalLayer (BlowupChart R t x)
    (chartBase R t x t) j, ∀ r : R, ∀ i : ℕ,
    (L (Polynomial.C (Ideal.Quotient.mk (Ideal.span {t,x}) r) * Polynomial.X^i)).val =
    principalLayerMap (BlowupChart R t x) (chartBase R t x t) j
    (chartBase R t x r * (chartSlope R t x)^i) := by sorry
