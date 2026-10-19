-- Prove2me | Theorems.Thm_TypeDensity_residueKillX_apply_ker
-- name    : TypeDensity.residueKillX_apply_ker
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:41.579734+00:00
-- url     : https://prove2.me/theorems/15ef8773-0ae4-448f-8f61-7029ab82020c
-- title:
--   `residueKillX` sends constants to their residues, `T ↦ X` and `X ↦ 0`;
-- statement:
--   `residueKillX` sends constants to their residues, `T ↦ X` and `X ↦ 0`; it is surjective with kernel `(π, X)`, and it is compatible with the chart substitutions.
-- source:
--   TypeDensity/Blowup/NilpotentGluing.lean#L1181-L1256

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
import Theorems.Thm_TypeDensity_coeff_substAlgHom_kill
import Theorems.Thm_TypeDensity_mvPowerSeries_mem_span_C_var_iff
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

theorem TypeDensity.residueKillX_apply_ker (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (hpi : Irreducible pi) :
    (∀ c : O, residueKillX O (MvPowerSeries.C c) = PowerSeries.C (IsLocalRing.residue O c)) ∧
    residueKillX O (axisT O) = PowerSeries.X ∧ residueKillX O (axisX O) = 0 ∧ Function.Surjective
    (residueKillX O) ∧ RingHom.ker (residueKillX O) = Ideal.span
    {(MvPowerSeries.C pi : TwoSeries O), axisX O} ∧
    (∀ s : TwoSeries O, killX O (xChartSubst O s) = killT O s) ∧ ∀ s : TwoSeries O, killX O
    (chartSubst O 0 s) = killX O s := by sorry
