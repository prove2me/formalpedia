-- Prove2me | Theorems.Thm_TypeDensity_product_chart_projection
-- name    : TypeDensity.product_chart_projection
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:28.0397+00:00
-- url     : https://prove2.me/theorems/168e794a-1cad-4a96-8279-4e0bc18817a1
-- title:
--   A coordinate ideal of a product chart projects to the coordinate ideals of the component charts, membership is componentwise, and the chart is injective when all component charts are.
-- statement:
--   A coordinate ideal of a product chart projects to the coordinate ideals of the component charts, membership is componentwise, and the chart is injective when all component charts are.
-- source:
--   TypeDensity/Measure/Atlas.lean#L71-L99

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
import Theorems.Thm_TypeDensity_principal_ideal_image
import Theorems.Thm_TypeDensity_coordinateLift_smul_eq_mul
import Theorems.Thm_TypeDensity_pi_strict_transform_map_eval
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

theorem TypeDensity.product_chart_projection (O : Type) [CommRing O] (ι : Type) [Finite ι] (Oj : ι → Type)
    [∀ j, CommRing (Oj j)] [∀ j, Algebra O (Oj j)] (R : ι → Type) [∀ j, CommRing (R j)]
    [∀ j, Algebra O (R j)] [∀ j, Algebra (Oj j) (R j)] [∀ j, IsScalarTower O (Oj j) (R j)]
    (nn : ι → ℕ) (n : ℕ) (ρ : (Fin n → O) ≃ₗ[O] (∀ j, Fin (nn j) → Oj j))
    (bc' : ∀ j, Fin (nn j) → R j) (bc : Fin n → ∀ j, R j)
    (hcompat : ∀ (w : Fin n → O) (j : ι), coordinateLift bc w j = coordinateLift (bc' j) (ρ w j))
    (g : ∀ j, R j) (pi : O) (pij : ∀ j, Oj j) (hpi : ∀ j, algebraMap O (Oj j) pi = pij j) :
    (∀ (w : Fin n → O) (j : ι), (coordinateIdeal pi g bc w).map (Pi.evalRingHom R j) =
      coordinateIdeal (pij j) (g j) (bc' j) (ρ w j)) ∧
      (∀ (w : Fin n → O) (x : ∀ j, R j), x ∈ coordinateIdeal pi g bc w ↔ ∀ j,
      x j ∈ coordinateIdeal (pij j) (g j) (bc' j) (ρ w j)) ∧
      ((∀ j, Function.Injective (coordinateIdeal (pij j) (g j) (bc' j))) →
      Function.Injective (coordinateIdeal pi g bc)) := by sorry
