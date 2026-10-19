-- Prove2me | Theorems.Thm_TypeDensity_lawCoeff_lawProd_descend_eval
-- name    : TypeDensity.lawCoeff_lawProd_descend_eval
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:32:25.778364+00:00
-- url     : https://prove2.me/theorems/e75013bf-01be-47d2-91dd-2ef091462cee
-- title:
--   lawCoeff lawProd descend eval
-- statement:
--   For a list `l` of pairs `(δⱼ, sⱼ)` with all `δⱼ > 0`, the `σ`-coefficient at `q` of the product of the descended state laws `lawDescend δⱼ (stateLaw sⱼ)` equals the sum over families of types `τⱼ` (each occurring in `stateLaw sⱼ`) with `σ = Σⱼ δⱼ·τⱼ` of the products of the `τⱼ`-coefficients of `stateLaw sⱼ` evaluated at `q^δⱼ`.
-- source:
--   TypeDensity/Recursion/Events.lean#L51-L68

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
import Definitions.Def_TypeDensity_Recursion_ChildMembers
import Theorems.Thm_TypeDensity_law_coeff_prod_descend
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

theorem TypeDensity.lawCoeff_lawProd_descend_eval (l : List (ℕ × State)) (hδ : ∀ z ∈ l, 0 < z.1)
    (σ : FactorType) (q : ℚ) :
    (lawCoeff (lawProd (l.map fun z => lawDescend z.1 (stateLaw z.2))) σ).eval q =
    ∑ τ ∈ Fintype.piFinset (fun j : Fin l.length => ((stateLaw (l.get j).2).map Prod.fst).toFinset),
      (if σ = ∑ j, scaleType (l.get j).1 (τ j) then
        ∏ j, (lawCoeff (stateLaw (l.get j).2) (τ j)).eval (q ^ (l.get j).1) else 0) := by sorry
