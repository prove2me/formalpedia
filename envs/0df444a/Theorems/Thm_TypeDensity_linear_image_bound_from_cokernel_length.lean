-- Prove2me | Theorems.Thm_TypeDensity_linear_image_bound_from_cokernel_length
-- name    : TypeDensity.linear_image_bound_from_cokernel_length
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:00:50.883121+00:00
-- url     : https://prove2.me/theorems/8ecccc08-c705-4452-9b6e-b5d65d8eb1ca
-- title:
--   If `coker D` has length `k` over a local ring with principal maximal ideal `(π)`, then `π ^ k • w ∈ range D` for every `w`.
-- statement:
--   If `coker D` has length `k` over a local ring with principal maximal ideal `(π)`, then `π ^ k • w ∈ range D` for every `w`.
-- source:
--   TypeDensity/Measure/HenselProducts.lean#L704-L721

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Theorems.Thm_TypeDensity_maximal_ideal_power_kills
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
set_option autoImplicit false

open TypeDensity
open MeasureTheory
open scoped BigOperators ENNReal

theorem TypeDensity.linear_image_bound_from_cokernel_length (O V W : Type) [CommRing O] [IsLocalRing O]
    [AddCommGroup V] [Module O V] [AddCommGroup W] [Module O W] (pi : O)
    (hpi : IsLocalRing.maximalIdeal O = Ideal.span {pi}) (D : V →ₗ[O] W) (k : ℕ)
    (hk : Module.length O (W ⧸ D.range) = k) :
    ∀ w : W, (pi^k) • w ∈ D.range := by sorry
