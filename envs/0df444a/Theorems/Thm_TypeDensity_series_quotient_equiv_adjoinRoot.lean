-- Prove2me | Theorems.Thm_TypeDensity_series_quotient_equiv_adjoinRoot
-- name    : TypeDensity.series_quotient_equiv_adjoinRoot
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:25:37.201816+00:00
-- url     : https://prove2.me/theorems/7fb5e38c-40ce-494c-aa1b-c8057468b610
-- title:
--   For monic `F` of degree `r > 0` whose lower coefficients lie in the maximal ideal, the quotient of the concrete surface `(1, 1, 0)` by `F(x)` is `O`-isomorphic to `AdjoinRoot F`, compatibly with evalu
-- statement:
--   For monic `F` of degree `r > 0` whose lower coefficients lie in the maximal ideal, the quotient of the concrete surface `(1, 1, 0)` by `F(x)` is `O`-isomorphic to `AdjoinRoot F`, compatibly with evaluation of polynomials at `x`.
-- source:
--   TypeDensity/Recursion/OrderDefect.lean#L663-L733

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Blowup_Directions
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Definitions.Def_TypeDensity_Formula_FiniteFieldCounts
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Formula_PatternCounts
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
import Definitions.Def_TypeDensity_Recursion_OrderDefect
import Theorems.Thm_TypeDensity_concrete_surface_quotient_T_equiv
import Theorems.Thm_TypeDensity_concrete_surface_vertical
import Theorems.Thm_TypeDensity_residueKillT_apply_ker
import Theorems.Thm_TypeDensity_concrete_surface_curve_basis
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.RegularLocalRing.Defs
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
open scoped BigOperators ENNReal TensorProduct

theorem TypeDensity.series_quotient_equiv_adjoinRoot (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (pi : O)
    (hpi : Irreducible pi) (F : Polynomial O) (hF : F.Monic) (r : ℕ) (hr : 0 < r)
    (hdeg : F.natDegree = r) (hred : ∀ i : ℕ, i < r → F.coeff i ∈ IsLocalRing.maximalIdeal O) :
    ∃ e : (ConcreteSurface O pi 1 1 0 ⧸
        Ideal.span {Polynomial.aeval (surfaceX O pi 1 1 0) F}) ≃ₐ[O] AdjoinRoot F,
      ∀ P : Polynomial O, e (Ideal.Quotient.mk
        (Ideal.span {Polynomial.aeval (surfaceX O pi 1 1 0) F})
        (Polynomial.aeval (surfaceX O pi 1 1 0) P)) = AdjoinRoot.mk F P := by sorry
