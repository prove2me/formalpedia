-- Prove2me | Theorems.Thm_TypeDensity_primitive_iff_residue_ne_zero
-- name    : TypeDensity.primitive_iff_residue_ne_zero
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:05.165747+00:00
-- url     : https://prove2.me/theorems/ab89c8bb-dc93-4a1e-b81b-7822563fea8d
-- title:
--   A coefficient vector is primitive iff its reduction is nonzero.
-- statement:
--   A coefficient vector is primitive iff its reduction is nonzero.
-- source:
--   TypeDensity/Unramified/PolynomialTypes.lean#L164-L172

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
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
open scoped ENNReal

theorem TypeDensity.primitive_iff_residue_ne_zero (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ)
    (a : Fin (n + 1) → O) :
    primitive O a ↔ residueVector O a ≠ 0 := by sorry
