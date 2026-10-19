-- Prove2me | Theorems.Thm_TypeDensity_strict_chart_coordinates_commute
-- name    : TypeDensity.strict_chart_coordinates_commute
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:23.978212+00:00
-- url     : https://prove2.me/theorems/cf1faa56-d1fe-4b4c-8e63-e798251d8648
-- title:
--   Chart coordinates commute with strict transforms: the strict transform of the coordinate ideal at `pi ^ (s + a - 1) • z` is the coordinate ideal at the child coordinate map of `z`.
-- statement:
--   Chart coordinates commute with strict transforms: the strict transform of the coordinate ideal at `pi ^ (s + a - 1) • z` is the coordinate ideal at the child coordinate map of `z`.
-- source:
--   TypeDensity/Blowup/StrictNormalizer.lean#L847-L875

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
import Theorems.Thm_TypeDensity_principal_ideal_unit_invariance
import Theorems.Thm_TypeDensity_scalar_normalizer_raises_order
import Theorems.Thm_TypeDensity_adic_perturb_bijective
import Theorems.Thm_TypeDensity_scaled_normalization_identity
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

theorem TypeDensity.strict_chart_coordinates_commute (O R C : Type) [CommRing O] [CommRing R] [CommRing C]
    [Algebra O R] [Algebra O C] (n : ℕ) (pi : O) (s a d : ℕ) (alpha : R →ₐ[O] C) (f : R) (g e c : C)
    (b : Fin n → R) (hf : alpha f = e ^ d * g) (hpi : (algebraMap O C pi) ^ s = e ^ d * c)
    (he : Function.Injective (fun z : C => e*z)) (ha : 0 < a)
    (hjac : algebraMap O C pi ∈ Ideal.jacobson (⊥ : Ideal C)) (bc : Fin n → C)
    (E : C ≃ₗ[O] ((Fin n → O) × C)) (hE : ∀ w, E.symm w = divisionMap g bc w)
    [IsAdicComplete (Ideal.span {pi}) ((Fin n → O) × C)] (z : Fin n → O) :
    strictTransformIdeal alpha e d (coordinateIdeal pi f b (coordinateScale pi (s+a-1) z)) =
      coordinateIdeal pi g bc (childCoordinateMap pi a bc E (pulledVariation alpha c b) z) := by sorry
