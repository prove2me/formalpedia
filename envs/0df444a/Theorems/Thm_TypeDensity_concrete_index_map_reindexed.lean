-- Prove2me | Theorems.Thm_TypeDensity_concrete_index_map_reindexed
-- name    : TypeDensity.concrete_index_map_reindexed
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:54:11.494729+00:00
-- url     : https://prove2.me/theorems/fc7ac716-6f9e-4182-9b6d-9db8a1ccf0d9
-- title:
--   The index map of a curve on a concrete surface, reindexed along an enumeration `e` of the points of its two-chart curve data: an injective `O`-algebra map from `R/(f)` into the product of the local cu
-- statement:
--   The index map of a curve on a concrete surface, reindexed along an enumeration `e` of the points of its two-chart curve data, is an injective `O`-algebra map from `R/(f)` into the product of the local curve orders, with cokernel of length `d(d-1)/2`.
-- source:
--   TypeDensity/Recursion/Termination.lean#L51-L142

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
import Definitions.Def_TypeDensity_Blowup_TwoChartCurveData
import Definitions.Def_TypeDensity_Surfaces_ConcreteAtlas
import Definitions.Def_TypeDensity_Recursion_Members
import Definitions.Def_TypeDensity_Measure_MemberCharts
import Definitions.Def_TypeDensity_Recursion_Termination
import Theorems.Thm_TypeDensity_concrete_curve_order_index
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
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
set_option autoImplicit false

open TypeDensity
open IsLocalRing MeasureTheory
open scoped BigOperators ENNReal

theorem TypeDensity.concrete_index_map_reindexed (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
    (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ) (ha : 0 < a)
    (beta : BlowupRestriction (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b)) (D : TwoChartCurveData (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b) beta) (f : ConcreteSurface O pi u a b)
    (G : GluedGenerators (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)
    beta (curveDataDegree D)) (hf : ∀ j : ℕ, surfaceToCechInput (ConcreteSurface O pi u a b)
    (surfaceT O pi u a b) (surfaceX O pi u a b) j f = (cechInputLattice (ConcreteSurface O pi u a b)
    (surfaceT O pi u a b) (surfaceX O pi u a b) j).mkQ (gluedFunctionPair
    (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b) G j))
    (hG : ∀ j : ℕ, Ideal.span {Ideal.Quotient.mk ((chartExceptional (ConcreteSurface O pi u a b)
    (surfaceT O pi u a b) (surfaceX O pi u a b))^j) (G.left j)} = leftLevelKernel D j ∧ Ideal.span
    {Ideal.Quotient.mk ((chartExceptional (ConcreteSurface O pi u a b) (surfaceX O pi u a b)
    (surfaceT O pi u a b))^j) (G.right j)} = rightLevelKernel D j) (n : ℕ) (e : Fin n ≃ AllPoints D)
    (B : Fin n → Type) [∀ j, CommRing (B j)] [∀ j, Algebra O (B j)]
    (eB : ∀ j, B j ≃+* (localRing D (e j) ⧸ Ideal.span {localCurve D (e j)}))
    (hB : ∀ (j : Fin n) (c : O), (eB j) (algebraMap O (B j) c) = Ideal.Quotient.mk
    (Ideal.span {localCurve D (e j)}) (localFromSurface D (e j)
    (algebraMap O (ConcreteSurface O pi u a b) c))) :
    ∃ ψ : ((ConcreteSurface O pi u a b) ⧸ Ideal.span {f}) →ₐ[O] ∀ j, B j, Function.Injective ψ ∧
      Module.length O ((∀ j, B j) ⧸ LinearMap.range ψ.toLinearMap) =
      (chooseTwo (curveDataDegree D) : ℕ∞) ∧ ∀ (r : (ConcreteSurface O pi u a b)) (j : Fin n),
      (eB j) (ψ (Ideal.Quotient.mk (Ideal.span {f}) r) j) = Ideal.Quotient.mk
      (Ideal.span {localCurve D (e j)}) (localFromSurface D (e j) r) := by sorry
