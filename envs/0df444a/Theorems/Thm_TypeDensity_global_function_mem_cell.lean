-- Prove2me | Theorems.Thm_TypeDensity_global_function_mem_cell
-- name    : TypeDensity.global_function_mem_cell
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:44:54.741393+00:00
-- url     : https://prove2.me/theorems/3f65b790-5b22-4b5a-a51d-cc01cbadf10c
-- title:
--   A global function glued from a curve datum matching `Dv`, whose strict transforms are the prescribed child ideals, generates an ideal of the fixed tangent cell.
-- statement:
--   A global function glued from a curve datum matching `Dv`, whose strict transforms are the prescribed child ideals, generates an ideal of the fixed tangent cell.
-- source:
--   TypeDensity/Blowup/DivisorPoints.lean#L1338-L1448

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
import Theorems.Thm_TypeDensity_directionPoint_properties
import Theorems.Thm_TypeDensity_count_normalizedFactors_divisorAffinePolynomial
import Theorems.Thm_TypeDensity_glued_level_one_data
import Theorems.Thm_TypeDensity_global_function_has_tangent_divisor
import Theorems.Thm_TypeDensity_infinity_point_maximal
import Theorems.Thm_TypeDensity_concrete_infinity_boundary_contact
import Theorems.Thm_TypeDensity_concrete_zero_boundary_contact
import Theorems.Thm_TypeDensity_concrete_strict_transform_generators
import Theorems.Thm_TypeDensity_blowupChart_concrete_isNoetherianRing
import Theorems.Thm_TypeDensity_concrete_surface_regular_pair_tx
import Theorems.Thm_TypeDensity_concrete_surface_regular_pair_xt
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

theorem TypeDensity.global_function_mem_cell (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)] (pi : O)
    (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ) (ha : 0 < a)
    [IsDomain (ConcreteSurface O pi u a b)] [IsRegularLocalRing (ConcreteSurface O pi u a b)]
    (S : SurfaceData O (ConcreteSurface O pi u a b))
    (hS : S.t = surfaceT O pi u a b ∧ S.x = surfaceX O pi u a b ∧ S.a = a ∧ S.b = b)
    (e : ((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) ⧸ (chartExceptional (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) ≃+*
      Polynomial (IsLocalRing.ResidueField (ConcreteSurface O pi u a b)))
    (he : ∀ r : ConcreteSurface O pi u a b, e (Ideal.Quotient.mk ((chartExceptional (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)))
      ((chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) r)) = Polynomial.C (IsLocalRing.residue (ConcreteSurface O pi u a b) r))
    (heZ : e (Ideal.Quotient.mk ((chartExceptional (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) ((chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)))) = Polynomial.X)
    (Dv : ExceptionalDivisor (IsLocalRing.ResidueField (ConcreteSurface O pi u a b)))
    (hinf : (infinityPoint (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b)).IsPrime) (s : State) (d : ℕ) (hd : 0 < d)
    (hs : (∃ c : ℕ, s = State.single a c ∧ b = 0) ∨ (∃ c h : ℕ, s = State.crossing a b c h ∧ 0 < b))
    (hdc : d ≤ stateContactT s) (hdh : ∀ h : ℕ, stateContactX s = some h → d ≤ h)
    (hDinf : 0 < Dv none ↔ d < stateContactT s)
    (hDzero : ∀ h : ℕ, stateContactX s = some h →
      (0 < Dv (zeroDirection (IsLocalRing.ResidueField (ConcreteSurface O pi u a b))) ↔ d < h))
    (beta : BlowupRestriction (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b))
    (D : TwoChartCurveData (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)
      beta)
    (hm : MatchesDivisor e D Dv) (hdD : curveDataDegree D = d) (f : ConcreteSurface O pi u a b)
    (G : GluedGenerators (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)
      beta d)
    (hf : ∀ j : ℕ, surfaceToCechInput (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b) j f = (cechInputLattice (ConcreteSurface O pi u a b)
        (surfaceT O pi u a b) (surfaceX O pi u a b) j).mkQ (gluedFunctionPair
          (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b) G j))
    (hG : ∀ j : ℕ,
      Ideal.span {Ideal.Quotient.mk ((chartExceptional (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))^j) (G.left j)} = leftLevelKernel D j ∧
      Ideal.span {Ideal.Quotient.mk ((chartExceptional (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b))^j) (G.right j)} = rightLevelKernel D j)
    (I : ∀ Q : divisorSupport Dv, Ideal (divisorLocalRing (ConcreteSurface O pi u a b)
      (surfaceT O pi u a b) (surfaceX O pi u a b) e Dv hinf Q))
    (hI : ∀ Q : divisorSupport Dv, I Q ∈ childIdealSet (ConcreteSurface O pi u a b)
      (surfaceT O pi u a b) (surfaceX O pi u a b) e Dv hinf s d Q)
    (hIf : ∀ Q : divisorSupport Dv, divisorStrictTransform (ConcreteSurface O pi u a b)
      (surfaceT O pi u a b) (surfaceX O pi u a b) e Dv hinf d (Ideal.span {f}) Q = I Q) :
    Ideal.span {f} ∈ (fixedTangentCell O (ConcreteSurface O pi u a b) S s d Dv) := by sorry
