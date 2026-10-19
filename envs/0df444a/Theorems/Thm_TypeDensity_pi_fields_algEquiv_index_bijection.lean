-- Prove2me | Theorems.Thm_TypeDensity_pi_fields_algEquiv_index_bijection
-- name    : TypeDensity.pi_fields_algEquiv_index_bijection
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:05.517199+00:00
-- url     : https://prove2.me/theorems/007b3c2e-dbd3-4f6e-8860-99ae9e778d11
-- title:
--   A `K`-algebra isomorphism of finite products of fields `∏ Lᵢ ≃ ∏ L'ⱼ` is induced by a bijection `π` of the index sets and isomorphisms `Lᵢ ≃ L'_{π i}`.
-- statement:
--   A `K`-algebra isomorphism of finite products of fields `∏ Lᵢ ≃ ∏ L'ⱼ` is induced by a bijection `π` of the index sets and isomorphisms `Lᵢ ≃ L'_{π i}`.
-- source:
--   TypeDensity/Unramified/FactorCells.lean#L416-L458

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
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
set_option autoImplicit false

open TypeDensity
open scoped ENNReal
open scoped Classical

theorem TypeDensity.pi_fields_algEquiv_index_bijection (K ι ι' : Type) [Field K]
    (L : ι → Type) (L' : ι' → Type) [∀ i, Field (L i)] [∀ i, Field (L' i)]
    [∀ i, Algebra K (L i)] [∀ i, Algebra K (L' i)] (e : (∀ i, L i) ≃ₐ[K] (∀ i, L' i)) :
    ∃ π : ι ≃ ι', ∀ i, e (Pi.single i (1 : L i)) = Pi.single (π i) (1 : L' (π i)) ∧
      ∃ φ : L i ≃ₐ[K] L' (π i), ∀ x : L i, e (Pi.single i x) = Pi.single (π i) (φ x) := by sorry
