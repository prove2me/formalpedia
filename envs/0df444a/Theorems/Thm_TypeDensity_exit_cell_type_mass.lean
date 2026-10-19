-- Prove2me | Theorems.Thm_TypeDensity_exit_cell_type_mass
-- name    : TypeDensity.exit_cell_type_mass
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:53:02.229744+00:00
-- url     : https://prove2.me/theorems/e385c2f8-95cd-4cb5-b939-b81ec7d7b3fe
-- title:
--   Mass of the type-`σ` box of a non-self (exit) cell: the divisor probability of the cell times the `σ`-coefficient of the product of the descended children laws, times the volume of the state set.
-- statement:
--   The mass of the type-`σ` box of a non-self (exit) cell is the divisor probability of the cell times the `σ`-coefficient of the product of the descended children laws, times the volume of the state set.
-- source:
--   TypeDensity/Recursion/Events.lean#L200-L259

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
import Theorems.Thm_TypeDensity_children_residue_degree_pos
import Theorems.Thm_TypeDensity_density_value_arith
import Theorems.Thm_TypeDensity_law_coeff_prod_formula
import Theorems.Thm_TypeDensity_nonself_child_rank_lt
import Theorems.Thm_TypeDensity_divisor_probability_pos
import Theorems.Thm_TypeDensity_child_volume_ratio
import Theorems.Thm_TypeDensity_terminates_type_unique
import Theorems.Thm_TypeDensity_universe_basic_facts
import Theorems.Thm_TypeDensity_lawCoeff_lawProd_descend_eval
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

theorem TypeDensity.exit_cell_type_mass (U : SurfaceUniverse) (i : U.ι) (hnt : (U.M i).s.terminal = false)
    (hIH : ∀ i' : U.ι, (U.M i').s.rank < (U.M i).s.rank → U.LawStatement i') (c : U.exitCells i)
    (σ : FactorType) :
    (U.M i).μ (U.typeBox i c.1 σ) =
      densityValue (.mul (divisorProbability (U.M i).s ((U.M i).cellDegree c.1))
        (lawCoeff (lawProd (((U.M i).childList c.1).map fun z ↦ lawDescend z.1 (stateLaw z.2))) σ))
        (U.M i).q * (U.M i).μ (U.M i).stateSet := by sorry
