-- Prove2me | Theorems.Thm_TypeDensity_concrete_strict_transform_multiplicity
-- name    : TypeDensity.concrete_strict_transform_multiplicity
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:31:36.072983+00:00
-- url     : https://prove2.me/theorems/56e2e8dd-df7f-42a8-a89c-55cc7a99d337
-- title:
--   The local intersection length of the strict transform with the exceptional divisor at the point `P` equals the multiplicity of the irreducible factor `φ` (defining `P`) in the reduced tangent form `∑
-- statement:
--   The local intersection length of the strict transform with the exceptional divisor at the point `P` equals the multiplicity of the irreducible factor `φ` (defining `P`) in the reduced tangent form `∑ cᵢ Xⁱ`.
-- source:
--   TypeDensity/Blowup/StrictNormalizer.lean#L177-L253

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
import Theorems.Thm_TypeDensity_rootMultiplicity_map_eq_count_normalizedFactors
import Theorems.Thm_TypeDensity_concrete_strict_transform_residue_series
import Theorems.Thm_TypeDensity_concrete_surface_equiv_curve_length_and_regular
import Theorems.Thm_TypeDensity_concrete_surface_quotient_parameters_equiv
import Theorems.Thm_TypeDensity_concrete_surface_maximalIdeal_eq
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
open scoped Classical

theorem TypeDensity.concrete_strict_transform_multiplicity (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a) (d : ℕ) (c : Fin (d + 1) → ConcreteSurface O pi u a b)
    (hne : ∃ i : Fin (d + 1), c i ∉ Ideal.span {(surfaceT O pi u a b), (surfaceX O pi u a b)})
    [IsLocalRing (ConcreteSurface O pi u a b)]
    (P : Ideal (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b))) [P.IsMaximal] [P.IsPrime]
    (hP : (chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))
    (surfaceT O pi u a b) ∈ P) (e : ((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b)) ⧸ chartExceptional (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b)) ≃+* Polynomial (IsLocalRing.ResidueField (ConcreteSurface O pi u a b)))
    (he : ∀ r : (ConcreteSurface O pi u a b), e
    (Ideal.Quotient.mk (chartExceptional (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b)) ((chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b)) r)) = Polynomial.C (IsLocalRing.residue (ConcreteSurface O pi u a b) r))
    (heZ : e (Ideal.Quotient.mk (chartExceptional (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b)) (chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b))) = Polynomial.X) (φ : Polynomial
    (IsLocalRing.ResidueField (ConcreteSurface O pi u a b))) (hφ : φ.Monic ∧ Irreducible φ)
    (hPφ : (P.map (Ideal.Quotient.mk (chartExceptional (ConcreteSurface O pi u a b)
    (surfaceT O pi u a b) (surfaceX O pi u a b)))).map e = Ideal.span {φ}) : Module.length
    (CompletedLocalAt (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b)) P) (CompletedLocalAt
    (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) P ⧸
    Ideal.span {completedPointMap (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b)) P (∑ i : Fin (d+1), algebraMap (ConcreteSurface O pi u a b)
    (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) (c i) *
    (chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))^i.val),
    completedPointMap (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b)) P ((chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b)) (surfaceT O pi u a b))}) =
    (Multiset.count φ (UniqueFactorizationMonoid.normalizedFactors
    (∑ i : Fin (d+1), Polynomial.C (IsLocalRing.residue (ConcreteSurface O pi u a b) (c i)) *
    Polynomial.X^i.val : Polynomial (IsLocalRing.ResidueField (ConcreteSurface O pi u a b)))) :
    ℕ∞) := by sorry
