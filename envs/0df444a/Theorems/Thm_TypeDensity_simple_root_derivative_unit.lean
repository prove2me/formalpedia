-- Prove2me | Theorems.Thm_TypeDensity_simple_root_derivative_unit
-- name    : TypeDensity.simple_root_derivative_unit
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:31:56.51553+00:00
-- url     : https://prove2.me/theorems/88ad812d-1356-4197-bcc8-dbbb5857a19e
-- title:
--   An approximate root of `Φ` in `O[X]/(Φ)` (a root modulo `𝔪`) is a simple root: the derivative of `Φ` there is a unit, already modulo `𝔪`.
-- statement:
--   An approximate root of `Φ` in `O[X]/(Φ)` (a root modulo `𝔪`) is a simple root: the derivative of `Φ` there is a unit, already modulo `𝔪`.
-- source:
--   TypeDensity/Unramified/FrobeniusDescent.lean#L339-L362

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_base_ideal_maximal_local
import Theorems.Thm_TypeDensity_residue_extension_field
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
import Mathlib.RingTheory.Henselian
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.simple_root_derivative_unit (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) (a : AdjoinRoot Φ)
    (ha : baseReduce O Φ ((Φ.map (AdjoinRoot.of Φ)).eval a) = 0) :
    IsUnit (baseReduce O Φ ((Φ.map (AdjoinRoot.of Φ)).derivative.eval a)) ∧
      IsUnit ((Φ.map (AdjoinRoot.of Φ)).derivative.eval a) := by sorry
