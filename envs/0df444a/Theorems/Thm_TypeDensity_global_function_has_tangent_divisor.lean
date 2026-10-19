-- Prove2me | Theorems.Thm_TypeDensity_global_function_has_tangent_divisor
-- name    : TypeDensity.global_function_has_tangent_divisor
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:25:45.437818+00:00
-- url     : https://prove2.me/theorems/0e735d62-3978-4a5a-9721-dd0e39944a6f
-- title:
--   A global function glued from the generators of a curve datum matching `Dv` has tangent divisor `Dv` in degree `deg D`.
-- statement:
--   A global function glued from the generators of a curve datum matching `Dv` has tangent divisor `Dv` in degree `deg D`.
-- source:
--   TypeDensity/Blowup/DivisorPoints.lean#L1251-L1290

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
import Theorems.Thm_TypeDensity_glued_level_one_data
import Theorems.Thm_TypeDensity_initial_form_lift_independent
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

theorem TypeDensity.global_function_has_tangent_divisor (O R : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CommRing R] [IsDomain R] [Algebra O R] [IsRegularLocalRing R]
    (S : SurfaceData O R) (beta : BlowupRestriction R S.t S.x)
    (D : TwoChartCurveData R S.t S.x beta) (Dv : ExceptionalDivisor (IsLocalRing.ResidueField R))
    (e : (BlowupChart R S.t S.x ⧸ chartExceptional R S.t S.x) ≃+*
      Polynomial (IsLocalRing.ResidueField R))
    (he : ∀ r : R, e (Ideal.Quotient.mk (chartExceptional R S.t S.x) (chartBase R S.t S.x r)) =
      Polynomial.C (IsLocalRing.residue R r))
    (heZ : e (Ideal.Quotient.mk (chartExceptional R S.t S.x) (chartSlope R S.t S.x)) = Polynomial.X)
    (hm : MatchesDivisor e D Dv) [IsNoetherianRing (BlowupChart R S.t S.x)]
    [IsNoetherianRing (BlowupChart R S.x S.t)] (hreg : RegularParameterPair R S.t S.x)
    (hregSwap : RegularParameterPair R S.x S.t) (f : R)
    (G : GluedGenerators R S.t S.x beta (curveDataDegree D))
    (hf : ∀ j : ℕ, surfaceToCechInput R S.t S.x j f =
      (cechInputLattice R S.t S.x j).mkQ (gluedFunctionPair R S.t S.x G j))
    (hG : ∀ j : ℕ,
      Ideal.span {Ideal.Quotient.mk ((chartExceptional R S.t S.x)^j) (G.left j)} =
        leftLevelKernel D j ∧
      Ideal.span {Ideal.Quotient.mk ((chartExceptional R S.x S.t)^j) (G.right j)} =
        rightLevelKernel D j) :
    HasTangentDivisor O R S (Ideal.span {f}) (curveDataDegree D) Dv := by sorry
