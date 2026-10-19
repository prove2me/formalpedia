-- Prove2me | Theorems.Thm_TypeDensity_product_first_order_expansion
-- name    : TypeDensity.product_first_order_expansion
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:08.389268+00:00
-- url     : https://prove2.me/theorems/212fb95a-dc06-471c-af56-9711b35d7294
-- title:
--   First-order expansion of a product: `∏ (G i + E i) ≡ ∏ G i + ∑ E i ∏_{j ≠ i} G j` modulo `J²` when all `E i ∈ J`.
-- statement:
--   First-order expansion of a product: `∏ (G i + E i) ≡ ∏ G i + ∑ E i ∏_{j ≠ i} G j` modulo `J²` when all `E i ∈ J`.
-- source:
--   TypeDensity/Unramified/PolynomialTypes.lean#L174-L206

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
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
import Mathlib.RingTheory.Henselian
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms
set_option autoImplicit false

open TypeDensity
open scoped ENNReal
open scoped Classical

theorem TypeDensity.product_first_order_expansion (A ι : Type) [CommRing A] (J : Ideal A) (G E : ι → A)
    (hE : ∀ i, E i ∈ J) (s : Finset ι) :
    ∏ i ∈ s, (G i + E i) - ∏ i ∈ s, G i - ∑ i ∈ s, E i * ∏ j ∈ s.erase i, G j ∈ J ^ 2 := by sorry
